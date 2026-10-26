import V185TrunkScan23Chunk0511

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_3027788 : List Nat := [2, 2, 1, 3, 3, 2, 3, 2, 1, 1, 3]
def baseStart_3027788 : Nat := 118140960795 + 3027788 * 2 ^ 59
def prefixEnd_3027788 : Nat := 4983230072969 + 3 ^ 40 * 3027788 * 2
def baseEnd_3027788 : Nat := 1554710563915504999225463

theorem tailTrace_3027788 : CollatzResearch.WordTrace tailWord_3027788 prefixEnd_3027788 1554710563915504999225463 := by
  unfold tailWord_3027788
  simp only [CollatzResearch.WordTrace]
  refine ⟨55216250377424327933338009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73621667169899103911117345 55216250377424327933338009)
  ·
    refine ⟨41412187783068245950003507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55216250377424327933338009 41412187783068245950003507)
    ·
      refine ⟨62118281674602368925005261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41412187783068245950003507 62118281674602368925005261)
      ·
        refine ⟨23294355627975888346876973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62118281674602368925005261 23294355627975888346876973)
        ·
          refine ⟨8735383360490958130078865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23294355627975888346876973 8735383360490958130078865)
          ·
            refine ⟨6551537520368218597559149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8735383360490958130078865 6551537520368218597559149)
            ·
              refine ⟨2456826570138081974084681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6551537520368218597559149 2456826570138081974084681)
              ·
                refine ⟨1842619927603561480563511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2456826570138081974084681 1842619927603561480563511)
                ·
                  refine ⟨2763929891405342220845267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1842619927603561480563511 2763929891405342220845267)
                  ·
                    refine ⟨4145894837108013331267901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2763929891405342220845267 4145894837108013331267901)
                    ·
                      refine ⟨1554710563915504999225463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4145894837108013331267901 1554710563915504999225463)
                      ·
                        rfl

theorem cell23_3027788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 3, 2, 1, 1, 3].length) (baseStart_3027788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3027788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3027788 prefixEnd_3027788 := by exact prefixLift 3027788
  have htrace : WordTrace (prefixWord ++ tailWord_3027788) baseStart_3027788 baseEnd_3027788 := by
    simpa [prefixWord, tailWord_3027788, baseEnd_3027788] using wordTrace_append hprefix tailTrace_3027788
  have hstable : (prefixWord ++ tailWord_3027788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3027788).length < 2 ^ (prefixWord ++ tailWord_3027788).sum := by decide
  have hdescent : baseEnd_3027788 < baseStart_3027788 := by decide
  rcases family_descends (prefixWord ++ tailWord_3027788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3027797 : List Nat := [1, 3, 2, 2, 2, 1, 2, 2, 3, 2, 3]
def baseStart_3027797 : Nat := 118140960795 + 3027797 * 2 ^ 59
def prefixEnd_3027797 : Nat := 4983230072969 + 3 ^ 40 * 3027797 * 2
def baseEnd_3027797 : Nat := 1554715185241395464012921

theorem tailTrace_3027797 : CollatzResearch.WordTrace tailWord_3027797 prefixEnd_3027797 1554715185241395464012921 := by
  unfold tailWord_3027797
  simp only [CollatzResearch.WordTrace]
  refine ⟨110432829011816050403753645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73621886007877366935835763 110432829011816050403753645)
  ·
    refine ⟨41412310879431018901407617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 110432829011816050403753645 41412310879431018901407617)
    ·
      refine ⟨31059233159573264176055713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41412310879431018901407617 31059233159573264176055713)
      ·
        refine ⟨23294424869679948132041785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31059233159573264176055713 23294424869679948132041785)
        ·
          refine ⟨17470818652259961099031339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23294424869679948132041785 17470818652259961099031339)
          ·
            refine ⟨26206227978389941648547009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17470818652259961099031339 26206227978389941648547009)
            ·
              refine ⟨19654670983792456236410257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26206227978389941648547009 19654670983792456236410257)
              ·
                refine ⟨14741003237844342177307693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19654670983792456236410257 14741003237844342177307693)
                ·
                  refine ⟨5527876214191628316490385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14741003237844342177307693 5527876214191628316490385)
                  ·
                    refine ⟨4145907160643721237367789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5527876214191628316490385 4145907160643721237367789)
                    ·
                      refine ⟨1554715185241395464012921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4145907160643721237367789 1554715185241395464012921)
                      ·
                        rfl

theorem cell23_3027797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 2, 2, 3, 2, 3].length) (baseStart_3027797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3027797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3027797 prefixEnd_3027797 := by exact prefixLift 3027797
  have htrace : WordTrace (prefixWord ++ tailWord_3027797) baseStart_3027797 baseEnd_3027797 := by
    simpa [prefixWord, tailWord_3027797, baseEnd_3027797] using wordTrace_append hprefix tailTrace_3027797
  have hstable : (prefixWord ++ tailWord_3027797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3027797).length < 2 ^ (prefixWord ++ tailWord_3027797).sum := by decide
  have hdescent : baseEnd_3027797 < baseStart_3027797 := by decide
  rcases family_descends (prefixWord ++ tailWord_3027797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3027827 : List Nat := [1, 1, 1, 2, 2, 1, 4, 1, 6, 1, 3]
def baseStart_3027827 : Nat := 118140960795 + 3027827 * 2 ^ 59
def prefixEnd_3027827 : Nat := 4983230072969 + 3 ^ 40 * 3027827 * 2
def baseEnd_3027827 : Nat := 1554730589661030346637783

theorem tailTrace_3027827 : CollatzResearch.WordTrace tailWord_3027827 prefixEnd_3027827 1554730589661030346637783 := by
  unfold tailWord_3027827
  simp only [CollatzResearch.WordTrace]
  refine ⟨110433923201707365527345735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73622615467804910351563823 110433923201707365527345735)
  ·
    refine ⟨165650884802561048291018603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110433923201707365527345735 165650884802561048291018603)
    ·
      refine ⟨248476327203841572436527905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165650884802561048291018603 248476327203841572436527905)
      ·
        refine ⟨186357245402881179327395929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 248476327203841572436527905 186357245402881179327395929)
        ·
          refine ⟨139767934052160884495546947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 186357245402881179327395929 139767934052160884495546947)
          ·
            refine ⟨209651901078241326743320421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 139767934052160884495546947 209651901078241326743320421)
            ·
              refine ⟨39309731452170248764372579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 209651901078241326743320421 39309731452170248764372579)
              ·
                refine ⟨58964597178255373146558869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39309731452170248764372579 58964597178255373146558869)
                ·
                  refine ⟨2763965492730720616244947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 58964597178255373146558869 2763965492730720616244947)
                  ·
                    refine ⟨4145948239096080924367421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2763965492730720616244947 4145948239096080924367421)
                    ·
                      refine ⟨1554730589661030346637783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4145948239096080924367421 1554730589661030346637783)
                      ·
                        rfl

theorem cell23_3027827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 1, 6, 1, 3].length) (baseStart_3027827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3027827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3027827 prefixEnd_3027827 := by exact prefixLift 3027827
  have htrace : WordTrace (prefixWord ++ tailWord_3027827) baseStart_3027827 baseEnd_3027827 := by
    simpa [prefixWord, tailWord_3027827, baseEnd_3027827] using wordTrace_append hprefix tailTrace_3027827
  have hstable : (prefixWord ++ tailWord_3027827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3027827).length < 2 ^ (prefixWord ++ tailWord_3027827).sum := by decide
  have hdescent : baseEnd_3027827 < baseStart_3027827 := by decide
  rcases family_descends (prefixWord ++ tailWord_3027827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3027838 : List Nat := [4, 2, 3, 1, 2, 1, 2, 2, 2, 4]
def baseStart_3027838 : Nat := 118140960795 + 3027838 * 2 ^ 59
def prefixEnd_3027838 : Nat := 4983230072969 + 3 ^ 40 * 3027838 * 2
def baseEnd_3027838 : Nat := 518245412649409934533411

theorem tailTrace_3027838 : CollatzResearch.WordTrace tailWord_3027838 prefixEnd_3027838 518245412649409934533411 := by
  unfold tailWord_3027838
  simp only [CollatzResearch.WordTrace]
  refine ⟨13804290550583439300749521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 73622882936445009603997445 13804290550583439300749521)
  ·
    refine ⟨10353217912937579475562141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13804290550583439300749521 10353217912937579475562141)
    ·
      refine ⟨3882456717351592303335803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10353217912937579475562141 3882456717351592303335803)
      ·
        refine ⟨5823685076027388455003705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3882456717351592303335803 5823685076027388455003705)
        ·
          refine ⟨4367763807020541341252779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5823685076027388455003705 4367763807020541341252779)
          ·
            refine ⟨6551645710530812011879169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4367763807020541341252779 6551645710530812011879169)
            ·
              refine ⟨4913734282898109008909377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6551645710530812011879169 4913734282898109008909377)
              ·
                refine ⟨3685300712173581756682033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4913734282898109008909377 3685300712173581756682033)
                ·
                  refine ⟨2763975534130186317511525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3685300712173581756682033 2763975534130186317511525)
                  ·
                    refine ⟨518245412649409934533411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2763975534130186317511525 518245412649409934533411)
                    ·
                      rfl

theorem cell23_3027838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 2, 2, 2, 4].length) (baseStart_3027838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3027838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3027838 prefixEnd_3027838 := by exact prefixLift 3027838
  have htrace : WordTrace (prefixWord ++ tailWord_3027838) baseStart_3027838 baseEnd_3027838 := by
    simpa [prefixWord, tailWord_3027838, baseEnd_3027838] using wordTrace_append hprefix tailTrace_3027838
  have hstable : (prefixWord ++ tailWord_3027838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3027838).length < 2 ^ (prefixWord ++ tailWord_3027838).sum := by decide
  have hdescent : baseEnd_3027838 < baseStart_3027838 := by decide
  rcases family_descends (prefixWord ++ tailWord_3027838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3027845 : List Nat := [1, 3, 1, 1, 3, 5, 2, 2, 1, 2, 2]
def baseStart_3027845 : Nat := 118140960795 + 3027845 * 2 ^ 59
def prefixEnd_3027845 : Nat := 4983230072969 + 3 ^ 40 * 3027845 * 2
def baseEnd_3027845 : Nat := 1554739832312811276212701

theorem tailTrace_3027845 : CollatzResearch.WordTrace tailWord_3027845 prefixEnd_3027845 1554739832312811276212701 := by
  unfold tailWord_3027845
  simp only [CollatzResearch.WordTrace]
  refine ⟨110434579715642154601500989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73623053143761436401000659 110434579715642154601500989)
  ·
    refine ⟨41412967393365807975562871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 110434579715642154601500989 41412967393365807975562871)
    ·
      refine ⟨62119451090048711963344307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41412967393365807975562871 62119451090048711963344307)
      ·
        refine ⟨93179176635073067945016461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62119451090048711963344307 93179176635073067945016461)
        ·
          refine ⟨34942191238152400479381173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 93179176635073067945016461 34942191238152400479381173)
          ·
            refine ⟨3275830428576787544941985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 34942191238152400479381173 3275830428576787544941985)
            ·
              refine ⟨2456872821432590658706489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3275830428576787544941985 2456872821432590658706489)
              ·
                refine ⟨1842654616074442994029867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2456872821432590658706489 1842654616074442994029867)
                ·
                  refine ⟨2763981924111664491044801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1842654616074442994029867 2763981924111664491044801)
                  ·
                    refine ⟨2072986443083748368283601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2763981924111664491044801 2072986443083748368283601)
                    ·
                      refine ⟨1554739832312811276212701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2072986443083748368283601 1554739832312811276212701)
                      ·
                        rfl

theorem cell23_3027845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 5, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 5, 2, 2, 1, 2, 2].length) (baseStart_3027845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3027845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3027845 prefixEnd_3027845 := by exact prefixLift 3027845
  have htrace : WordTrace (prefixWord ++ tailWord_3027845) baseStart_3027845 baseEnd_3027845 := by
    simpa [prefixWord, tailWord_3027845, baseEnd_3027845] using wordTrace_append hprefix tailTrace_3027845
  have hstable : (prefixWord ++ tailWord_3027845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3027845).length < 2 ^ (prefixWord ++ tailWord_3027845).sum := by decide
  have hdescent : baseEnd_3027845 < baseStart_3027845 := by decide
  rcases family_descends (prefixWord ++ tailWord_3027845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3027884 : List Nat := [2, 2, 1, 1, 1, 1, 2, 3, 6, 2, 2]
def baseStart_3027884 : Nat := 118140960795 + 3027884 * 2 ^ 59
def prefixEnd_3027884 : Nat := 4983230072969 + 3 ^ 40 * 3027884 * 2
def baseEnd_3027884 : Nat := 1554759858058336623625021

theorem tailTrace_3027884 : CollatzResearch.WordTrace tailWord_3027884 prefixEnd_3027884 1554759858058336623625021 := by
  unfold tailWord_3027884
  simp only [CollatzResearch.WordTrace]
  refine ⟨55218001081250432131085353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73624001441667242841447137 55218001081250432131085353)
  ·
    refine ⟨41413500810937824098314015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55218001081250432131085353 41413500810937824098314015)
    ·
      refine ⟨62120251216406736147471023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41413500810937824098314015 62120251216406736147471023)
      ·
        refine ⟨93180376824610104221206535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62120251216406736147471023 93180376824610104221206535)
        ·
          refine ⟨139770565236915156331809803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93180376824610104221206535 139770565236915156331809803)
          ·
            refine ⟨209655847855372734497714705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 139770565236915156331809803 209655847855372734497714705)
            ·
              refine ⟨157241885891529550873286029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 209655847855372734497714705 157241885891529550873286029)
              ·
                refine ⟨58965707209323581577482261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 157241885891529550873286029 58965707209323581577482261)
                ·
                  refine ⟨2764017525437042886444481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 58965707209323581577482261 2764017525437042886444481)
                  ·
                    refine ⟨2073013144077782164833361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2764017525437042886444481 2073013144077782164833361)
                    ·
                      refine ⟨1554759858058336623625021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2073013144077782164833361 1554759858058336623625021)
                      ·
                        rfl

theorem cell23_3027884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 6, 2, 2].length) (baseStart_3027884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3027884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3027884 prefixEnd_3027884 := by exact prefixLift 3027884
  have htrace : WordTrace (prefixWord ++ tailWord_3027884) baseStart_3027884 baseEnd_3027884 := by
    simpa [prefixWord, tailWord_3027884, baseEnd_3027884] using wordTrace_append hprefix tailTrace_3027884
  have hstable : (prefixWord ++ tailWord_3027884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3027884).length < 2 ^ (prefixWord ++ tailWord_3027884).sum := by decide
  have hdescent : baseEnd_3027884 < baseStart_3027884 := by decide
  rcases family_descends (prefixWord ++ tailWord_3027884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3027897 : List Nat := [1, 2, 1, 4, 2, 2, 1, 2, 2, 2, 4]
def baseStart_3027897 : Nat := 118140960795 + 3027897 * 2 ^ 59
def prefixEnd_3027897 : Nat := 4983230072969 + 3 ^ 40 * 3027897 * 2
def baseEnd_3027897 : Nat := 1554766533306845072762461

theorem tailTrace_3027897 : CollatzResearch.WordTrace tailWord_3027897 prefixEnd_3027897 1554766533306845072762461 := by
  unfold tailWord_3027897
  simp only [CollatzResearch.WordTrace]
  refine ⟨110436476311453767482393945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73624317540969178321595963 110436476311453767482393945)
  ·
    refine ⟨82827357233590325611795459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110436476311453767482393945 82827357233590325611795459)
    ·
      refine ⟨124241035850385488417693189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82827357233590325611795459 124241035850385488417693189)
      ·
        refine ⟨23295194221947279078317473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 124241035850385488417693189 23295194221947279078317473)
        ·
          refine ⟨17471395666460459308738105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23295194221947279078317473 17471395666460459308738105)
          ·
            refine ⟨13103546749845344481553579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17471395666460459308738105 13103546749845344481553579)
            ·
              refine ⟨19655320124768016722330369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13103546749845344481553579 19655320124768016722330369)
              ·
                refine ⟨14741490093576012541747777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19655320124768016722330369 14741490093576012541747777)
                ·
                  refine ⟨11056117570182009406310833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14741490093576012541747777 11056117570182009406310833)
                  ·
                    refine ⟨8292088177636507054733125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11056117570182009406310833 8292088177636507054733125)
                    ·
                      refine ⟨1554766533306845072762461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8292088177636507054733125 1554766533306845072762461)
                      ·
                        rfl

theorem cell23_3027897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 1, 2, 2, 2, 4].length) (baseStart_3027897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3027897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3027897 prefixEnd_3027897 := by exact prefixLift 3027897
  have htrace : WordTrace (prefixWord ++ tailWord_3027897) baseStart_3027897 baseEnd_3027897 := by
    simpa [prefixWord, tailWord_3027897, baseEnd_3027897] using wordTrace_append hprefix tailTrace_3027897
  have hstable : (prefixWord ++ tailWord_3027897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3027897).length < 2 ^ (prefixWord ++ tailWord_3027897).sum := by decide
  have hdescent : baseEnd_3027897 < baseStart_3027897 := by decide
  rcases family_descends (prefixWord ++ tailWord_3027897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3027937 : List Nat := [1, 2, 3, 1, 2, 1, 1, 5, 2, 5]
def baseStart_3027937 : Nat := 118140960795 + 3027937 * 2 ^ 59
def prefixEnd_3027937 : Nat := 4983230072969 + 3 ^ 40 * 3027937 * 2
def baseEnd_3027937 : Nat := 518262357511008305420759

theorem tailTrace_3027937 : CollatzResearch.WordTrace tailWord_3027937 prefixEnd_3027937 518262357511008305420759 := by
  unfold tailWord_3027937
  simp only [CollatzResearch.WordTrace]
  refine ⟨110437935231308854313850065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73625290154205902875900043 110437935231308854313850065)
  ·
    refine ⟨82828451423481640735387549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110437935231308854313850065 82828451423481640735387549)
    ·
      refine ⟨31060669283805615275770331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82828451423481640735387549 31060669283805615275770331)
      ·
        refine ⟨46591003925708422913655497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31060669283805615275770331 46591003925708422913655497)
        ·
          refine ⟨34943252944281317185241623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46591003925708422913655497 34943252944281317185241623)
          ·
            refine ⟨52414879416421975777862435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34943252944281317185241623 52414879416421975777862435)
            ·
              refine ⟨78622319124632963666793653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52414879416421975777862435 78622319124632963666793653)
              ·
                refine ⟨7370842417934340343761905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 78622319124632963666793653 7370842417934340343761905)
                ·
                  refine ⟨5528131813450755257821429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7370842417934340343761905 5528131813450755257821429)
                  ·
                    refine ⟨518262357511008305420759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5528131813450755257821429 518262357511008305420759)
                    ·
                      rfl

theorem cell23_3027937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 5, 2, 5].length) (baseStart_3027937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3027937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3027937 prefixEnd_3027937 := by exact prefixLift 3027937
  have htrace : WordTrace (prefixWord ++ tailWord_3027937) baseStart_3027937 baseEnd_3027937 := by
    simpa [prefixWord, tailWord_3027937, baseEnd_3027937] using wordTrace_append hprefix tailTrace_3027937
  have hstable : (prefixWord ++ tailWord_3027937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3027937).length < 2 ^ (prefixWord ++ tailWord_3027937).sum := by decide
  have hdescent : baseEnd_3027937 < baseStart_3027937 := by decide
  rcases family_descends (prefixWord ++ tailWord_3027937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3027958 : List Nat := [5, 1, 1, 1, 3, 2, 3, 2, 5]
def baseStart_3027958 : Nat := 118140960795 + 3027958 * 2 ^ 59
def prefixEnd_3027958 : Nat := 4983230072969 + 3 ^ 40 * 3027958 * 2
def baseEnd_3027958 : Nat := 172755317291863259344409

theorem tailTrace_3027958 : CollatzResearch.WordTrace tailWord_3027958 prefixEnd_3027958 172755317291863259344409 := by
  unfold tailWord_3027958
  simp only [CollatzResearch.WordTrace]
  refine ⟨6902418822764548431272783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 73625800776155183266909685 6902418822764548431272783)
  ·
    refine ⟨10353628234146822646909175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6902418822764548431272783 10353628234146822646909175)
    ·
      refine ⟨15530442351220233970363763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10353628234146822646909175 15530442351220233970363763)
      ·
        refine ⟨23295663526830350955545645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15530442351220233970363763 23295663526830350955545645)
        ·
          refine ⟨8735873822561381608329617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23295663526830350955545645 8735873822561381608329617)
          ·
            refine ⟨6551905366921036206247213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8735873822561381608329617 6551905366921036206247213)
            ·
              refine ⟨2456964512595388577342705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6551905366921036206247213 2456964512595388577342705)
              ·
                refine ⟨1842723384446541433007029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2456964512595388577342705 1842723384446541433007029)
                ·
                  refine ⟨172755317291863259344409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1842723384446541433007029 172755317291863259344409)
                  ·
                    rfl

theorem cell23_3027958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 3, 2, 5].length) (baseStart_3027958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3027958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3027958 prefixEnd_3027958 := by exact prefixLift 3027958
  have htrace : WordTrace (prefixWord ++ tailWord_3027958) baseStart_3027958 baseEnd_3027958 := by
    simpa [prefixWord, tailWord_3027958, baseEnd_3027958] using wordTrace_append hprefix tailTrace_3027958
  have hstable : (prefixWord ++ tailWord_3027958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3027958).length < 2 ^ (prefixWord ++ tailWord_3027958).sum := by decide
  have hdescent : baseEnd_3027958 < baseStart_3027958 := by decide
  rcases family_descends (prefixWord ++ tailWord_3027958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3027977 : List Nat := [1, 2, 1, 1, 3, 1, 1, 3, 3, 4, 3]
def baseStart_3027977 : Nat := 118140960795 + 3027977 * 2 ^ 59
def prefixEnd_3027977 : Nat := 4983230072969 + 3 ^ 40 * 3027977 * 2
def baseEnd_3027977 : Nat := 1554807611759204759762093

theorem tailTrace_3027977 : CollatzResearch.WordTrace tailWord_3027977 prefixEnd_3027977 1554807611759204759762093 := by
  unfold tailWord_3027977
  simp only [CollatzResearch.WordTrace]
  refine ⟨110439394151163941145306185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73626262767442627430204123 110439394151163941145306185)
  ·
    refine ⟨82829545613372955858979639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110439394151163941145306185 82829545613372955858979639)
    ·
      refine ⟨124244318420059433788469459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82829545613372955858979639 124244318420059433788469459)
      ·
        refine ⟨186366477630089150682704189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124244318420059433788469459 186366477630089150682704189)
        ·
          refine ⟨69887429111283431506014071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 186366477630089150682704189 69887429111283431506014071)
          ·
            refine ⟨104831143666925147259021107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69887429111283431506014071 104831143666925147259021107)
            ·
              refine ⟨157246715500387720888531661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 104831143666925147259021107 157246715500387720888531661)
              ·
                refine ⟨58967518312645395333199373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 157246715500387720888531661 58967518312645395333199373)
                ·
                  refine ⟨22112819367242023249949765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 58967518312645395333199373 22112819367242023249949765)
                  ·
                    refine ⟨4146153631357879359365581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22112819367242023249949765 4146153631357879359365581)
                    ·
                      refine ⟨1554807611759204759762093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4146153631357879359365581 1554807611759204759762093)
                      ·
                        rfl

theorem cell23_3027977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 3, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 3, 3, 4, 3].length) (baseStart_3027977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3027977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3027977 prefixEnd_3027977 := by exact prefixLift 3027977
  have htrace : WordTrace (prefixWord ++ tailWord_3027977) baseStart_3027977 baseEnd_3027977 := by
    simpa [prefixWord, tailWord_3027977, baseEnd_3027977] using wordTrace_append hprefix tailTrace_3027977
  have hstable : (prefixWord ++ tailWord_3027977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3027977).length < 2 ^ (prefixWord ++ tailWord_3027977).sum := by decide
  have hdescent : baseEnd_3027977 < baseStart_3027977 := by decide
  rcases family_descends (prefixWord ++ tailWord_3027977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3027991 : List Nat := [1, 1, 3, 5, 1, 2, 2, 1, 2, 1, 4]
def baseStart_3027991 : Nat := 118140960795 + 3027991 * 2 ^ 59
def prefixEnd_3027991 : Nat := 4983230072969 + 3 ^ 40 * 3027991 * 2
def baseEnd_3027991 : Nat := 1554814800488367704987029

theorem tailTrace_3027991 : CollatzResearch.WordTrace tailWord_3027991 prefixEnd_3027991 1554814800488367704987029 := by
  unfold tailWord_3027991
  simp only [CollatzResearch.WordTrace]
  refine ⟨110439904773113221536315827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73626603182075481024210551 110439904773113221536315827)
  ·
    refine ⟨165659857159669832304473741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110439904773113221536315827 165659857159669832304473741)
    ·
      refine ⟨62122446434876187114177653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 165659857159669832304473741 62122446434876187114177653)
      ·
        refine ⟨5823979353269642541954155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 62122446434876187114177653 5823979353269642541954155)
        ·
          refine ⟨8735969029904463812931233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5823979353269642541954155 8735969029904463812931233)
          ·
            refine ⟨6551976772428347859698425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8735969029904463812931233 6551976772428347859698425)
            ·
              refine ⟨4913982579321260894773819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6551976772428347859698425 4913982579321260894773819)
              ·
                refine ⟨7370973868981891342160729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4913982579321260894773819 7370973868981891342160729)
                ·
                  refine ⟨5528230401736418506620547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7370973868981891342160729 5528230401736418506620547)
                  ·
                    refine ⟨8292345602604627759930821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5528230401736418506620547 8292345602604627759930821)
                    ·
                      refine ⟨1554814800488367704987029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8292345602604627759930821 1554814800488367704987029)
                      ·
                        rfl

theorem cell23_3027991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 2, 1, 2, 1, 4].length) (baseStart_3027991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3027991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3027991 prefixEnd_3027991 := by exact prefixLift 3027991
  have htrace : WordTrace (prefixWord ++ tailWord_3027991) baseStart_3027991 baseEnd_3027991 := by
    simpa [prefixWord, tailWord_3027991, baseEnd_3027991] using wordTrace_append hprefix tailTrace_3027991
  have hstable : (prefixWord ++ tailWord_3027991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3027991).length < 2 ^ (prefixWord ++ tailWord_3027991).sum := by decide
  have hdescent : baseEnd_3027991 < baseStart_3027991 := by decide
  rcases family_descends (prefixWord ++ tailWord_3027991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3028017 : List Nat := [1, 2, 2, 3, 1, 2, 2, 1, 1, 2, 6]
def baseStart_3028017 : Nat := 118140960795 + 3028017 * 2 ^ 59
def prefixEnd_3028017 : Nat := 4983230072969 + 3 ^ 40 * 3028017 * 2
def baseEnd_3028017 : Nat := 1554828150985384603261909

theorem tailTrace_3028017 : CollatzResearch.WordTrace tailWord_3028017 prefixEnd_3028017 1554828150985384603261909 := by
  unfold tailWord_3028017
  simp only [CollatzResearch.WordTrace]
  refine ⟨110440853071019027976762305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73627235380679351984508203 110440853071019027976762305)
  ·
    refine ⟨82830639803264270982571729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110440853071019027976762305 82830639803264270982571729)
    ·
      refine ⟨62122979852448203236928797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82830639803264270982571729 62122979852448203236928797)
      ·
        refine ⟨23296117444668076213848299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62122979852448203236928797 23296117444668076213848299)
        ·
          refine ⟨34944176167002114320772449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23296117444668076213848299 34944176167002114320772449)
          ·
            refine ⟨26208132125251585740579337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34944176167002114320772449 26208132125251585740579337)
            ·
              refine ⟨19656099093938689305434503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26208132125251585740579337 19656099093938689305434503)
              ·
                refine ⟨29484148640908033958151755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19656099093938689305434503 29484148640908033958151755)
                ·
                  refine ⟨44226222961362050937227633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29484148640908033958151755 44226222961362050937227633)
                  ·
                    refine ⟨33169667221021538202920725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 44226222961362050937227633 33169667221021538202920725)
                    ·
                      refine ⟨1554828150985384603261909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 33169667221021538202920725 1554828150985384603261909)
                      ·
                        rfl

theorem cell23_3028017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 2, 1, 1, 2, 6].length) (baseStart_3028017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3028017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3028017 prefixEnd_3028017 := by exact prefixLift 3028017
  have htrace : WordTrace (prefixWord ++ tailWord_3028017) baseStart_3028017 baseEnd_3028017 := by
    simpa [prefixWord, tailWord_3028017, baseEnd_3028017] using wordTrace_append hprefix tailTrace_3028017
  have hstable : (prefixWord ++ tailWord_3028017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3028017).length < 2 ^ (prefixWord ++ tailWord_3028017).sum := by decide
  have hdescent : baseEnd_3028017 < baseStart_3028017 := by decide
  rcases family_descends (prefixWord ++ tailWord_3028017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3028044 : List Nat := [2, 2, 1, 3, 1, 1, 1, 6, 1, 5]
def baseStart_3028044 : Nat := 118140960795 + 3028044 * 2 ^ 59
def prefixEnd_3028044 : Nat := 4983230072969 + 3 ^ 40 * 3028044 * 2
def baseEnd_3028044 : Nat := 518280671654351999208095

theorem tailTrace_3028044 : CollatzResearch.WordTrace tailWord_3028044 prefixEnd_3028044 518280671654351999208095 := by
  unfold tailWord_3028044
  simp only [CollatzResearch.WordTrace]
  refine ⟨55220918920960605793997593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73627891894614141058663457 55220918920960605793997593)
  ·
    refine ⟨41415689190720454345498195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55220918920960605793997593 41415689190720454345498195)
    ·
      refine ⟨62123533786080681518247293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41415689190720454345498195 62123533786080681518247293)
      ·
        refine ⟨23296325169780255569342735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62123533786080681518247293 23296325169780255569342735)
        ·
          refine ⟨34944487754670383354014103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23296325169780255569342735 34944487754670383354014103)
          ·
            refine ⟨52416731632005575031021155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34944487754670383354014103 52416731632005575031021155)
            ·
              refine ⟨78625097448008362546531733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52416731632005575031021155 78625097448008362546531733)
              ·
                refine ⟨3685551442875391994368675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 78625097448008362546531733 3685551442875391994368675)
                ·
                  refine ⟨5528327164313087991553013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3685551442875391994368675 5528327164313087991553013)
                  ·
                    refine ⟨518280671654351999208095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5528327164313087991553013 518280671654351999208095)
                    ·
                      rfl

theorem cell23_3028044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 6, 1, 5].length) (baseStart_3028044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3028044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3028044 prefixEnd_3028044 := by exact prefixLift 3028044
  have htrace : WordTrace (prefixWord ++ tailWord_3028044) baseStart_3028044 baseEnd_3028044 := by
    simpa [prefixWord, tailWord_3028044, baseEnd_3028044] using wordTrace_append hprefix tailTrace_3028044
  have hstable : (prefixWord ++ tailWord_3028044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3028044).length < 2 ^ (prefixWord ++ tailWord_3028044).sum := by decide
  have hdescent : baseEnd_3028044 < baseStart_3028044 := by decide
  rcases family_descends (prefixWord ++ tailWord_3028044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3028057 : List Nat := [1, 2, 1, 2, 2, 1, 2, 3, 3, 6]
def baseStart_3028057 : Nat := 118140960795 + 3028057 * 2 ^ 59
def prefixEnd_3028057 : Nat := 4983230072969 + 3 ^ 40 * 3028057 * 2
def baseEnd_3028057 : Nat := 518282896737188148920575

theorem tailTrace_3028057 : CollatzResearch.WordTrace tailWord_3028057 prefixEnd_3028057 518282896737188148920575 := by
  unfold tailWord_3028057
  simp only [CollatzResearch.WordTrace]
  refine ⟨110442311990874114808218425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73628207993916076538812283 110442311990874114808218425)
  ·
    refine ⟨82831733993155586106163819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110442311990874114808218425 82831733993155586106163819)
    ·
      refine ⟨124247600989733379159245729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82831733993155586106163819 124247600989733379159245729)
      ·
        refine ⟨93185700742300034369434297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 124247600989733379159245729 93185700742300034369434297)
        ·
          refine ⟨69889275556725025777075723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93185700742300034369434297 69889275556725025777075723)
          ·
            refine ⟨104833913335087538665613585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69889275556725025777075723 104833913335087538665613585)
            ·
              refine ⟨78625435001315653999210189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 104833913335087538665613585 78625435001315653999210189)
              ·
                refine ⟨29484538125493370249703821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 78625435001315653999210189 29484538125493370249703821)
                ·
                  refine ⟨11056701797060013843638933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29484538125493370249703821 11056701797060013843638933)
                  ·
                    refine ⟨518282896737188148920575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11056701797060013843638933 518282896737188148920575)
                    ·
                      rfl

theorem cell23_3028057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 3, 3, 6].length) (baseStart_3028057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3028057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3028057 prefixEnd_3028057 := by exact prefixLift 3028057
  have htrace : WordTrace (prefixWord ++ tailWord_3028057) baseStart_3028057 baseEnd_3028057 := by
    simpa [prefixWord, tailWord_3028057, baseEnd_3028057] using wordTrace_append hprefix tailTrace_3028057
  have hstable : (prefixWord ++ tailWord_3028057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3028057).length < 2 ^ (prefixWord ++ tailWord_3028057).sum := by decide
  have hdescent : baseEnd_3028057 < baseStart_3028057 := by decide
  rcases family_descends (prefixWord ++ tailWord_3028057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3028087 : List Nat := [1, 1, 3, 1, 1, 4, 2, 10]
def baseStart_3028087 : Nat := 118140960795 + 3028087 * 2 ^ 59
def prefixEnd_3028087 : Nat := 4983230072969 + 3 ^ 40 * 3028087 * 2
def baseEnd_3028087 : Nat := 57587559060414789977281

theorem tailTrace_3028087 : CollatzResearch.WordTrace tailWord_3028087 prefixEnd_3028087 57587559060414789977281 := by
  unfold tailWord_3028087
  simp only [CollatzResearch.WordTrace]
  refine ⟨110443406180765429931810515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73628937453843619954540343 110443406180765429931810515)
  ·
    refine ⟨165665109271148144897715773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110443406180765429931810515 165665109271148144897715773)
    ·
      refine ⟨62124415976680554336643415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 165665109271148144897715773 62124415976680554336643415)
      ·
        refine ⟨93186623965020831504965123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62124415976680554336643415 93186623965020831504965123)
        ·
          refine ⟨139779935947531247257447685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93186623965020831504965123 139779935947531247257447685)
          ·
            refine ⟨26208737990162108860771441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 139779935947531247257447685 26208737990162108860771441)
            ·
              refine ⟨19656553492621581645578581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26208737990162108860771441 19656553492621581645578581)
              ·
                refine ⟨57587559060414789977281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 19656553492621581645578581 57587559060414789977281)
                ·
                  rfl

theorem cell23_3028087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 2, 10].length) (baseStart_3028087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3028087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3028087 prefixEnd_3028087 := by exact prefixLift 3028087
  have htrace : WordTrace (prefixWord ++ tailWord_3028087) baseStart_3028087 baseEnd_3028087 := by
    simpa [prefixWord, tailWord_3028087, baseEnd_3028087] using wordTrace_append hprefix tailTrace_3028087
  have hstable : (prefixWord ++ tailWord_3028087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3028087).length < 2 ^ (prefixWord ++ tailWord_3028087).sum := by decide
  have hdescent : baseEnd_3028087 < baseStart_3028087 := by decide
  rcases family_descends (prefixWord ++ tailWord_3028087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3028107 : List Nat := [1, 1, 1, 1, 4, 1, 1, 2, 1, 4, 6]
def baseStart_3028107 : Nat := 118140960795 + 3028107 * 2 ^ 59
def prefixEnd_3028107 : Nat := 4983230072969 + 3 ^ 40 * 3028107 * 2
def baseEnd_3028107 : Nat := 1554874364244289251136495

theorem tailTrace_3028107 : CollatzResearch.WordTrace tailWord_3028107 prefixEnd_3028107 1554874364244289251136495 := by
  unfold tailWord_3028107
  simp only [CollatzResearch.WordTrace]
  refine ⟨110444135640692973347538575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73629423760461982231692383 110444135640692973347538575)
  ·
    refine ⟨165666203461039460021307863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110444135640692973347538575 165666203461039460021307863)
    ·
      refine ⟨248499305191559190031961795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165666203461039460021307863 248499305191559190031961795)
      ·
        refine ⟨372748957787338785047942693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 248499305191559190031961795 372748957787338785047942693)
        ·
          refine ⟨69890429585126022196489255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 372748957787338785047942693 69890429585126022196489255)
          ·
            refine ⟨104835644377689033294733883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69890429585126022196489255 104835644377689033294733883)
            ·
              refine ⟨157253466566533549942100825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 104835644377689033294733883 157253466566533549942100825)
              ·
                refine ⟨117940099924900162456575619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 157253466566533549942100825 117940099924900162456575619)
                ·
                  refine ⟨176910149887350243684863429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 117940099924900162456575619 176910149887350243684863429)
                  ·
                    refine ⟨33170653103878170690911893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 176910149887350243684863429 33170653103878170690911893)
                    ·
                      refine ⟨1554874364244289251136495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 33170653103878170690911893 1554874364244289251136495)
                      ·
                        rfl

theorem cell23_3028107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 2, 1, 4, 6].length) (baseStart_3028107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3028107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3028107 prefixEnd_3028107 := by exact prefixLift 3028107
  have htrace : WordTrace (prefixWord ++ tailWord_3028107) baseStart_3028107 baseEnd_3028107 := by
    simpa [prefixWord, tailWord_3028107, baseEnd_3028107] using wordTrace_append hprefix tailTrace_3028107
  have hstable : (prefixWord ++ tailWord_3028107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3028107).length < 2 ^ (prefixWord ++ tailWord_3028107).sum := by decide
  have hdescent : baseEnd_3028107 < baseStart_3028107 := by decide
  rcases family_descends (prefixWord ++ tailWord_3028107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3028115 : List Nat := [1, 1, 1, 2, 1, 2, 7, 3, 1, 2, 2]
def baseStart_3028115 : Nat := 118140960795 + 3028115 * 2 ^ 59
def prefixEnd_3028115 : Nat := 4983230072969 + 3 ^ 40 * 3028115 * 2
def baseEnd_3028115 : Nat := 1554878472089525219836459

theorem tailTrace_3028115 : CollatzResearch.WordTrace tailWord_3028115 prefixEnd_3028115 1554878472089525219836459 := by
  unfold tailWord_3028115
  simp only [CollatzResearch.WordTrace]
  refine ⟨110444427424663990713829799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73629618283109327142553199 110444427424663990713829799)
  ·
    refine ⟨165666641136995986070744699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110444427424663990713829799 165666641136995986070744699)
    ·
      refine ⟨248499961705493979106117049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165666641136995986070744699 248499961705493979106117049)
      ·
        refine ⟨186374971279120484329587787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 248499961705493979106117049 186374971279120484329587787)
        ·
          refine ⟨279562456918680726494381681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 186374971279120484329587787 279562456918680726494381681)
          ·
            refine ⟨209671842689010544870786261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 279562456918680726494381681 209671842689010544870786261)
            ·
              refine ⟨4914183813023684645409053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 209671842689010544870786261 4914183813023684645409053)
              ·
                refine ⟨1842818929883881742028395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4914183813023684645409053 1842818929883881742028395)
                ·
                  refine ⟨2764228394825822613042593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1842818929883881742028395 2764228394825822613042593)
                  ·
                    refine ⟨2073171296119366959781945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2764228394825822613042593 2073171296119366959781945)
                    ·
                      refine ⟨1554878472089525219836459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2073171296119366959781945 1554878472089525219836459)
                      ·
                        rfl

theorem cell23_3028115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 7, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 7, 3, 1, 2, 2].length) (baseStart_3028115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3028115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3028115 prefixEnd_3028115 := by exact prefixLift 3028115
  have htrace : WordTrace (prefixWord ++ tailWord_3028115) baseStart_3028115 baseEnd_3028115 := by
    simpa [prefixWord, tailWord_3028115, baseEnd_3028115] using wordTrace_append hprefix tailTrace_3028115
  have hstable : (prefixWord ++ tailWord_3028115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3028115).length < 2 ^ (prefixWord ++ tailWord_3028115).sum := by decide
  have hdescent : baseEnd_3028115 < baseStart_3028115 := by decide
  rcases family_descends (prefixWord ++ tailWord_3028115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3028205 : List Nat := [1, 5, 1, 2, 2, 2, 2, 1, 1, 4, 2]
def baseStart_3028205 : Nat := 118140960795 + 3028205 * 2 ^ 59
def prefixEnd_3028205 : Nat := 4983230072969 + 3 ^ 40 * 3028205 * 2
def baseEnd_3028205 : Nat := 1554924685348429867711045

theorem tailTrace_3028205 : CollatzResearch.WordTrace tailWord_3028205 prefixEnd_3028205 1554924685348429867711045 := by
  unfold tailWord_3028205
  simp only [CollatzResearch.WordTrace]
  refine ⟨110447709994337936084606069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73631806662891957389737379 110447709994337936084606069)
  ·
    refine ⟨10354472811969181507931819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 110447709994337936084606069 10354472811969181507931819)
    ·
      refine ⟨15531709217953772261897729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10354472811969181507931819 15531709217953772261897729)
      ·
        refine ⟨11648781913465329196423297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15531709217953772261897729 11648781913465329196423297)
        ·
          refine ⟨8736586435098996897317473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11648781913465329196423297 8736586435098996897317473)
          ·
            refine ⟨6552439826324247672988105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8736586435098996897317473 6552439826324247672988105)
            ·
              refine ⟨4914329869743185754741079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6552439826324247672988105 4914329869743185754741079)
              ·
                refine ⟨7371494804614778632111619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4914329869743185754741079 7371494804614778632111619)
                ·
                  refine ⟨11057242206922167948167429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7371494804614778632111619 11057242206922167948167429)
                  ·
                    refine ⟨2073232913797906490281393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11057242206922167948167429 2073232913797906490281393)
                    ·
                      refine ⟨1554924685348429867711045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2073232913797906490281393 1554924685348429867711045)
                      ·
                        rfl

theorem cell23_3028205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 2, 1, 1, 4, 2].length) (baseStart_3028205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3028205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3028205 prefixEnd_3028205 := by exact prefixLift 3028205
  have htrace : WordTrace (prefixWord ++ tailWord_3028205) baseStart_3028205 baseEnd_3028205 := by
    simpa [prefixWord, tailWord_3028205, baseEnd_3028205] using wordTrace_append hprefix tailTrace_3028205
  have hstable : (prefixWord ++ tailWord_3028205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3028205).length < 2 ^ (prefixWord ++ tailWord_3028205).sum := by decide
  have hdescent : baseEnd_3028205 < baseStart_3028205 := by decide
  rcases family_descends (prefixWord ++ tailWord_3028205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3028226 : List Nat := [3, 4, 1, 1, 4, 1, 2, 1, 1, 3, 2]
def baseStart_3028226 : Nat := 118140960795 + 3028226 * 2 ^ 59
def prefixEnd_3028226 : Nat := 4983230072969 + 3 ^ 40 * 3028226 * 2
def baseEnd_3028226 : Nat := 1554935468442174285548449

theorem tailTrace_3028226 : CollatzResearch.WordTrace tailWord_3028226 prefixEnd_3028226 1554935468442174285548449 := by
  unfold tailWord_3028226
  simp only [CollatzResearch.WordTrace]
  refine ⟨27612118981815464167780133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73632317284841237780747021 27612118981815464167780133)
  ·
    refine ⟨5177272309090399531458775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27612118981815464167780133 5177272309090399531458775)
    ·
      refine ⟨7765908463635599297188163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5177272309090399531458775 7765908463635599297188163)
      ·
        refine ⟨11648862695453398945782245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7765908463635599297188163 11648862695453398945782245)
        ·
          refine ⟨2184161755397512302334171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11648862695453398945782245 2184161755397512302334171)
          ·
            refine ⟨3276242633096268453501257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2184161755397512302334171 3276242633096268453501257)
            ·
              refine ⟨2457181974822201340125943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3276242633096268453501257 2457181974822201340125943)
              ·
                refine ⟨3685772962233302010188915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2457181974822201340125943 3685772962233302010188915)
                ·
                  refine ⟨5528659443349953015283373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3685772962233302010188915 5528659443349953015283373)
                  ·
                    refine ⟨2073247291256232380731265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5528659443349953015283373 2073247291256232380731265)
                    ·
                      refine ⟨1554935468442174285548449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2073247291256232380731265 1554935468442174285548449)
                      ·
                        rfl

theorem cell23_3028226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 4, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 4, 1, 2, 1, 1, 3, 2].length) (baseStart_3028226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3028226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3028226 prefixEnd_3028226 := by exact prefixLift 3028226
  have htrace : WordTrace (prefixWord ++ tailWord_3028226) baseStart_3028226 baseEnd_3028226 := by
    simpa [prefixWord, tailWord_3028226, baseEnd_3028226] using wordTrace_append hprefix tailTrace_3028226
  have hstable : (prefixWord ++ tailWord_3028226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3028226).length < 2 ^ (prefixWord ++ tailWord_3028226).sum := by decide
  have hdescent : baseEnd_3028226 < baseStart_3028226 := by decide
  rcases family_descends (prefixWord ++ tailWord_3028226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3028228 : List Nat := [2, 3, 2, 2, 2, 1, 1, 5, 5]
def baseStart_3028228 : Nat := 118140960795 + 3028228 * 2 ^ 59
def prefixEnd_3028228 : Nat := 4983230072969 + 3 ^ 40 * 3028228 * 2
def baseEnd_3028228 : Nat := 172770721711498141969271

theorem tailTrace_3028228 : CollatzResearch.WordTrace tailWord_3028228 prefixEnd_3028228 172770721711498141969271 := by
  unfold tailWord_3028228
  simp only [CollatzResearch.WordTrace]
  refine ⟨55224274436627305506346669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73632365915503074008462225 55224274436627305506346669)
  ·
    refine ⟨20709102913735239564880001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55224274436627305506346669 20709102913735239564880001)
    ·
      refine ⟨15531827185301429673660001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20709102913735239564880001 15531827185301429673660001)
      ·
        refine ⟨11648870388976072255245001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15531827185301429673660001 11648870388976072255245001)
        ·
          refine ⟨8736652791732054191433751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11648870388976072255245001 8736652791732054191433751)
          ·
            refine ⟨13104979187598081287150627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8736652791732054191433751 13104979187598081287150627)
            ·
              refine ⟨19657468781397121930725941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13104979187598081287150627 19657468781397121930725941)
              ·
                refine ⟨1842887698255980181005557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 19657468781397121930725941 1842887698255980181005557)
                ·
                  refine ⟨172770721711498141969271, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1842887698255980181005557 172770721711498141969271)
                  ·
                    rfl

theorem cell23_3028228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 1, 5, 5].length) (baseStart_3028228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3028228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3028228 prefixEnd_3028228 := by exact prefixLift 3028228
  have htrace : WordTrace (prefixWord ++ tailWord_3028228) baseStart_3028228 baseEnd_3028228 := by
    simpa [prefixWord, tailWord_3028228, baseEnd_3028228] using wordTrace_append hprefix tailTrace_3028228
  have hstable : (prefixWord ++ tailWord_3028228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3028228).length < 2 ^ (prefixWord ++ tailWord_3028228).sum := by decide
  have hdescent : baseEnd_3028228 < baseStart_3028228 := by decide
  rcases family_descends (prefixWord ++ tailWord_3028228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3028261 : List Nat := [1, 3, 1, 2, 4, 1, 1, 2, 1, 3, 4]
def baseStart_3028261 : Nat := 118140960795 + 3028261 * 2 ^ 59
def prefixEnd_3028261 : Nat := 4983230072969 + 3 ^ 40 * 3028261 * 2
def baseEnd_3028261 : Nat := 1554953440265081648610787

theorem tailTrace_3028261 : CollatzResearch.WordTrace tailWord_3028261 prefixEnd_3028261 1554953440265081648610787 := by
  unfold tailWord_3028261
  simp only [CollatzResearch.WordTrace]
  refine ⟨110449752482135057648644637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73633168321423371765763091 110449752482135057648644637)
  ·
    refine ⟨41418657180800646618241739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 110449752482135057648644637 41418657180800646618241739)
    ·
      refine ⟨62127985771200969927362609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41418657180800646618241739 62127985771200969927362609)
      ·
        refine ⟨46595989328400727445521957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62127985771200969927362609 46595989328400727445521957)
        ·
          refine ⟨8736747999075136396035367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 46595989328400727445521957 8736747999075136396035367)
          ·
            refine ⟨13105121998612704594053051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8736747999075136396035367 13105121998612704594053051)
            ·
              refine ⟨19657682997919056891079577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13105121998612704594053051 19657682997919056891079577)
              ·
                refine ⟨14743262248439292668309683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19657682997919056891079577 14743262248439292668309683)
                ·
                  refine ⟨22114893372658939002464525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14743262248439292668309683 22114893372658939002464525)
                  ·
                    refine ⟨8293085014747102125924197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22114893372658939002464525 8293085014747102125924197)
                    ·
                      refine ⟨1554953440265081648610787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8293085014747102125924197 1554953440265081648610787)
                      ·
                        rfl

theorem cell23_3028261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 1, 2, 1, 3, 4].length) (baseStart_3028261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3028261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3028261 prefixEnd_3028261 := by exact prefixLift 3028261
  have htrace : WordTrace (prefixWord ++ tailWord_3028261) baseStart_3028261 baseEnd_3028261 := by
    simpa [prefixWord, tailWord_3028261, baseEnd_3028261] using wordTrace_append hprefix tailTrace_3028261
  have hstable : (prefixWord ++ tailWord_3028261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3028261).length < 2 ^ (prefixWord ++ tailWord_3028261).sum := by decide
  have hdescent : baseEnd_3028261 < baseStart_3028261 := by decide
  rcases family_descends (prefixWord ++ tailWord_3028261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3028351 : List Nat := [1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 4]
def baseStart_3028351 : Nat := 118140960795 + 3028351 * 2 ^ 59
def prefixEnd_3028351 : Nat := 4983230072969 + 3 ^ 40 * 3028351 * 2
def baseEnd_3028351 : Nat := 1554999653523986296485373

theorem tailTrace_3028351 : CollatzResearch.WordTrace tailWord_3028351 prefixEnd_3028351 1554999653523986296485373 := by
  unfold tailWord_3028351
  simp only [CollatzResearch.WordTrace]
  refine ⟨110453035051809003019420907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73635356701206002012947271 110453035051809003019420907)
  ·
    refine ⟨165679552577713504529131361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110453035051809003019420907 165679552577713504529131361)
    ·
      refine ⟨124259664433285128396848521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 165679552577713504529131361 124259664433285128396848521)
      ·
        refine ⟨93194748324963846297636391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 124259664433285128396848521 93194748324963846297636391)
        ·
          refine ⟨139792122487445769446454587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93194748324963846297636391 139792122487445769446454587)
          ·
            refine ⟨209688183731168654169681881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 139792122487445769446454587 209688183731168654169681881)
            ·
              refine ⟨157266137798376490627261411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 209688183731168654169681881 157266137798376490627261411)
              ·
                refine ⟨235899206697564735940892117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 157266137798376490627261411 235899206697564735940892117)
                ·
                  refine ⟨5528887656974173498614659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 235899206697564735940892117 5528887656974173498614659)
                  ·
                    refine ⟨8293331485461260247921989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5528887656974173498614659 8293331485461260247921989)
                    ·
                      refine ⟨1554999653523986296485373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8293331485461260247921989 1554999653523986296485373)
                      ·
                        rfl

theorem cell23_3028351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 4].length) (baseStart_3028351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3028351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3028351 prefixEnd_3028351 := by exact prefixLift 3028351
  have htrace : WordTrace (prefixWord ++ tailWord_3028351) baseStart_3028351 baseEnd_3028351 := by
    simpa [prefixWord, tailWord_3028351, baseEnd_3028351] using wordTrace_append hprefix tailTrace_3028351
  have hstable : (prefixWord ++ tailWord_3028351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3028351).length < 2 ^ (prefixWord ++ tailWord_3028351).sum := by decide
  have hdescent : baseEnd_3028351 < baseStart_3028351 := by decide
  rcases family_descends (prefixWord ++ tailWord_3028351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3028355 : List Nat := [1, 1, 1, 3, 5, 1, 2, 2, 2, 3, 2]
def baseStart_3028355 : Nat := 118140960795 + 3028355 * 2 ^ 59
def prefixEnd_3028355 : Nat := 4983230072969 + 3 ^ 40 * 3028355 * 2
def baseEnd_3028355 : Nat := 1555001707446604280835355

theorem tailTrace_3028355 : CollatzResearch.WordTrace tailWord_3028355 prefixEnd_3028355 1555001707446604280835355 := by
  unfold tailWord_3028355
  simp only [CollatzResearch.WordTrace]
  refine ⟨110453180943794511702566519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73635453962529674468377679 110453180943794511702566519)
  ·
    refine ⟨165679771415691767553849779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110453180943794511702566519 165679771415691767553849779)
    ·
      refine ⟨248519657123537651330774669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165679771415691767553849779 248519657123537651330774669)
      ·
        refine ⟨93194871421326619249040501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 248519657123537651330774669 93194871421326619249040501)
        ·
          refine ⟨8737019195749370554597547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 93194871421326619249040501 8737019195749370554597547)
          ·
            refine ⟨13105528793624055831896321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8737019195749370554597547 13105528793624055831896321)
            ·
              refine ⟨9829146595218041873922241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13105528793624055831896321 9829146595218041873922241)
              ·
                refine ⟨7371859946413531405441681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9829146595218041873922241 7371859946413531405441681)
                ·
                  refine ⟨5528894959810148554081261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7371859946413531405441681 5528894959810148554081261)
                  ·
                    refine ⟨2073335609928805707780473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5528894959810148554081261 2073335609928805707780473)
                    ·
                      refine ⟨1555001707446604280835355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2073335609928805707780473 1555001707446604280835355)
                      ·
                        rfl

theorem cell23_3028355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 2, 2, 2, 3, 2].length) (baseStart_3028355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3028355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3028355 prefixEnd_3028355 := by exact prefixLift 3028355
  have htrace : WordTrace (prefixWord ++ tailWord_3028355) baseStart_3028355 baseEnd_3028355 := by
    simpa [prefixWord, tailWord_3028355, baseEnd_3028355] using wordTrace_append hprefix tailTrace_3028355
  have hstable : (prefixWord ++ tailWord_3028355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3028355).length < 2 ^ (prefixWord ++ tailWord_3028355).sum := by decide
  have hdescent : baseEnd_3028355 < baseStart_3028355 := by decide
  rcases family_descends (prefixWord ++ tailWord_3028355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3028378 : List Nat := [3, 1, 1, 4, 1, 1, 4, 1, 1, 6]
def baseStart_3028378 : Nat := 118140960795 + 3028378 * 2 ^ 59
def prefixEnd_3028378 : Nat := 4983230072969 + 3 ^ 40 * 3028378 * 2
def baseEnd_3028378 : Nat := 518337839167219230282583

theorem tailTrace_3028378 : CollatzResearch.WordTrace tailWord_3028378 prefixEnd_3028378 518337839167219230282583 := by
  unfold tailWord_3028378
  simp only [CollatzResearch.WordTrace]
  refine ⟨27613504955677796657663447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73636013215140791087102525 27613504955677796657663447)
  ·
    refine ⟨41420257433516694986495171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27613504955677796657663447 41420257433516694986495171)
    ·
      refine ⟨62130386150275042479742757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41420257433516694986495171 62130386150275042479742757)
      ·
        refine ⟨11649447403176570464951767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 62130386150275042479742757 11649447403176570464951767)
        ·
          refine ⟨17474171104764855697427651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11649447403176570464951767 17474171104764855697427651)
          ·
            refine ⟨26211256657147283546141477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17474171104764855697427651 26211256657147283546141477)
            ·
              refine ⟨4914610623215115664901527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26211256657147283546141477 4914610623215115664901527)
              ·
                refine ⟨7371915934822673497352291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4914610623215115664901527 7371915934822673497352291)
                ·
                  refine ⟨11057873902234010246028437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7371915934822673497352291 11057873902234010246028437)
                  ·
                    refine ⟨518337839167219230282583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11057873902234010246028437 518337839167219230282583)
                    ·
                      rfl

theorem cell23_3028378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 4, 1, 1, 6].length) (baseStart_3028378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3028378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3028378 prefixEnd_3028378 := by exact prefixLift 3028378
  have htrace : WordTrace (prefixWord ++ tailWord_3028378) baseStart_3028378 baseEnd_3028378 := by
    simpa [prefixWord, tailWord_3028378, baseEnd_3028378] using wordTrace_append hprefix tailTrace_3028378
  have hstable : (prefixWord ++ tailWord_3028378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3028378).length < 2 ^ (prefixWord ++ tailWord_3028378).sum := by decide
  have hdescent : baseEnd_3028378 < baseStart_3028378 := by decide
  rcases family_descends (prefixWord ++ tailWord_3028378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3028462 : List Nat := [4, 1, 2, 1, 2, 1, 1, 5, 1, 3, 2]
def baseStart_3028462 : Nat := 118140960795 + 3028462 * 2 ^ 59
def prefixEnd_3028462 : Nat := 4983230072969 + 3 ^ 40 * 3028462 * 2
def baseEnd_3028462 : Nat := 1555056649876635362197363

theorem tailTrace_3028462 : CollatzResearch.WordTrace tailWord_3028462 prefixEnd_3028462 1555056649876635362197363 := by
  unfold tailWord_3028462
  simp only [CollatzResearch.WordTrace]
  refine ⟨13807135444300858622088955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 73638055702937912651141093 13807135444300858622088955)
  ·
    refine ⟨20710703166451287933133433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13807135444300858622088955 20710703166451287933133433)
    ·
      refine ⟨15533027374838465949850075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20710703166451287933133433 15533027374838465949850075)
      ·
        refine ⟨23299541062257698924775113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15533027374838465949850075 23299541062257698924775113)
        ·
          refine ⟨17474655796693274193581335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23299541062257698924775113 17474655796693274193581335)
          ·
            refine ⟨26211983695039911290372003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17474655796693274193581335 26211983695039911290372003)
            ·
              refine ⟨39317975542559866935558005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26211983695039911290372003 39317975542559866935558005)
              ·
                refine ⟨3686060207114987525208563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 39317975542559866935558005 3686060207114987525208563)
                ·
                  refine ⟨5529090310672481287812845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3686060207114987525208563 5529090310672481287812845)
                  ·
                    refine ⟨2073408866502180482929817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5529090310672481287812845 2073408866502180482929817)
                    ·
                      refine ⟨1555056649876635362197363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2073408866502180482929817 1555056649876635362197363)
                      ·
                        rfl

theorem cell23_3028462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 5, 1, 3, 2].length) (baseStart_3028462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3028462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3028462 prefixEnd_3028462 := by exact prefixLift 3028462
  have htrace : WordTrace (prefixWord ++ tailWord_3028462) baseStart_3028462 baseEnd_3028462 := by
    simpa [prefixWord, tailWord_3028462, baseEnd_3028462] using wordTrace_append hprefix tailTrace_3028462
  have hstable : (prefixWord ++ tailWord_3028462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3028462).length < 2 ^ (prefixWord ++ tailWord_3028462).sum := by decide
  have hdescent : baseEnd_3028462 < baseStart_3028462 := by decide
  rcases family_descends (prefixWord ++ tailWord_3028462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3028471 : List Nat := [1, 1, 3, 1, 1, 1, 1, 3, 2, 3, 6]
def baseStart_3028471 : Nat := 118140960795 + 3028471 * 2 ^ 59
def prefixEnd_3028471 : Nat := 4983230072969 + 3 ^ 40 * 3028471 * 2
def baseEnd_3028471 : Nat := 1555061271202525826984821

theorem tailTrace_3028471 : CollatzResearch.WordTrace tailWord_3028471 prefixEnd_3028471 1555061271202525826984821 := by
  unfold tailWord_3028471
  simp only [CollatzResearch.WordTrace]
  refine ⟨110457411811374263513789267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73638274540916175675859511 110457411811374263513789267)
  ·
    refine ⟨165686117717061395270683901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110457411811374263513789267 165686117717061395270683901)
    ·
      refine ⟨62132294143898023226506463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 165686117717061395270683901 62132294143898023226506463)
      ·
        refine ⟨93198441215847034839759695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62132294143898023226506463 93198441215847034839759695)
        ·
          refine ⟨139797661823770552259639543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93198441215847034839759695 139797661823770552259639543)
          ·
            refine ⟨209696492735655828389459315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 139797661823770552259639543 209696492735655828389459315)
            ·
              refine ⟨314544739103483742584188973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 209696492735655828389459315 314544739103483742584188973)
              ·
                refine ⟨117954277163806403469070865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 314544739103483742584188973 117954277163806403469070865)
                ·
                  refine ⟨88465707872854802601803149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 117954277163806403469070865 88465707872854802601803149)
                  ·
                    refine ⟨33174640452320550975676181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 88465707872854802601803149 33174640452320550975676181)
                    ·
                      refine ⟨1555061271202525826984821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 33174640452320550975676181 1555061271202525826984821)
                      ·
                        rfl

theorem cell23_3028471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 3, 2, 3, 6].length) (baseStart_3028471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3028471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3028471 prefixEnd_3028471 := by exact prefixLift 3028471
  have htrace : WordTrace (prefixWord ++ tailWord_3028471) baseStart_3028471 baseEnd_3028471 := by
    simpa [prefixWord, tailWord_3028471, baseEnd_3028471] using wordTrace_append hprefix tailTrace_3028471
  have hstable : (prefixWord ++ tailWord_3028471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3028471).length < 2 ^ (prefixWord ++ tailWord_3028471).sum := by decide
  have hdescent : baseEnd_3028471 < baseStart_3028471 := by decide
  rcases family_descends (prefixWord ++ tailWord_3028471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3028488 : List Nat := [2, 1, 3, 2, 1, 1, 2, 3, 2, 2, 4]
def baseStart_3028488 : Nat := 118140960795 + 3028488 * 2 ^ 59
def prefixEnd_3028488 : Nat := 4983230072969 + 3 ^ 40 * 3028488 * 2
def baseEnd_3028488 : Nat := 1555070000373652260472243

theorem tailTrace_3028488 : CollatzResearch.WordTrace tailWord_3028488 prefixEnd_3028488 1555070000373652260472243 := by
  unfold tailWord_3028488
  simp only [CollatzResearch.WordTrace]
  refine ⟨55229015926156337708579059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73638687901541783611438745 55229015926156337708579059)
  ·
    refine ⟨82843523889234506562868589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55229015926156337708579059 82843523889234506562868589)
    ·
      refine ⟨31066321458462939961075721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82843523889234506562868589 31066321458462939961075721)
      ·
        refine ⟨23299741093847204970806791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31066321458462939961075721 23299741093847204970806791)
        ·
          refine ⟨34949611640770807456210187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23299741093847204970806791 34949611640770807456210187)
          ·
            refine ⟨52424417461156211184315281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34949611640770807456210187 52424417461156211184315281)
            ·
              refine ⟨39318313095867158388236461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52424417461156211184315281 39318313095867158388236461)
              ·
                refine ⟨14744367410950184395588673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39318313095867158388236461 14744367410950184395588673)
                ·
                  refine ⟨11058275558212638296691505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14744367410950184395588673 11058275558212638296691505)
                  ·
                    refine ⟨8293706668659478722518629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11058275558212638296691505 8293706668659478722518629)
                    ·
                      refine ⟨1555070000373652260472243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8293706668659478722518629 1555070000373652260472243)
                      ·
                        rfl

theorem cell23_3028488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 3, 2, 2, 4].length) (baseStart_3028488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3028488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3028488 prefixEnd_3028488 := by exact prefixLift 3028488
  have htrace : WordTrace (prefixWord ++ tailWord_3028488) baseStart_3028488 baseEnd_3028488 := by
    simpa [prefixWord, tailWord_3028488, baseEnd_3028488] using wordTrace_append hprefix tailTrace_3028488
  have hstable : (prefixWord ++ tailWord_3028488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3028488).length < 2 ^ (prefixWord ++ tailWord_3028488).sum := by decide
  have hdescent : baseEnd_3028488 < baseStart_3028488 := by decide
  rcases family_descends (prefixWord ++ tailWord_3028488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3028526 : List Nat := [4, 1, 3, 1, 2, 2, 2, 2, 2, 2, 2]
def baseStart_3028526 : Nat := 118140960795 + 3028526 * 2 ^ 59
def prefixEnd_3028526 : Nat := 4983230072969 + 3 ^ 40 * 3028526 * 2
def baseEnd_3028526 : Nat := 1555089512638523111797069

theorem tailTrace_3028526 : CollatzResearch.WordTrace tailWord_3028526 prefixEnd_3028526 1555089512638523111797069 := by
  unfold tailWord_3028526
  simp only [CollatzResearch.WordTrace]
  refine ⟨13807427228271875988380179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 73639611884116671938027621 13807427228271875988380179)
  ·
    refine ⟨20711140842407813982570269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13807427228271875988380179 20711140842407813982570269)
    ·
      refine ⟨7766677815902930243463851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20711140842407813982570269 7766677815902930243463851)
      ·
        refine ⟨11650016723854395365195777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7766677815902930243463851 11650016723854395365195777)
        ·
          refine ⟨8737512542890796523896833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11650016723854395365195777 8737512542890796523896833)
          ·
            refine ⟨6553134407168097392922625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8737512542890796523896833 6553134407168097392922625)
            ·
              refine ⟨4914850805376073044691969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6553134407168097392922625 4914850805376073044691969)
              ·
                refine ⟨3686138104032054783518977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4914850805376073044691969 3686138104032054783518977)
                ·
                  refine ⟨2764603578024041087639233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3686138104032054783518977 2764603578024041087639233)
                  ·
                    refine ⟨2073452683518030815729425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2764603578024041087639233 2073452683518030815729425)
                    ·
                      refine ⟨1555089512638523111797069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2073452683518030815729425 1555089512638523111797069)
                      ·
                        rfl

theorem cell23_3028526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 2, 2, 2, 2, 2].length) (baseStart_3028526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3028526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3028526 prefixEnd_3028526 := by exact prefixLift 3028526
  have htrace : WordTrace (prefixWord ++ tailWord_3028526) baseStart_3028526 baseEnd_3028526 := by
    simpa [prefixWord, tailWord_3028526, baseEnd_3028526] using wordTrace_append hprefix tailTrace_3028526
  have hstable : (prefixWord ++ tailWord_3028526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3028526).length < 2 ^ (prefixWord ++ tailWord_3028526).sum := by decide
  have hdescent : baseEnd_3028526 < baseStart_3028526 := by decide
  rcases family_descends (prefixWord ++ tailWord_3028526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3028535 : List Nat := [1, 1, 3, 1, 2, 4, 1, 1, 2, 5, 2]
def baseStart_3028535 : Nat := 118140960795 + 3028535 * 2 ^ 59
def prefixEnd_3028535 : Nat := 4983230072969 + 3 ^ 40 * 3028535 * 2
def baseEnd_3028535 : Nat := 1555094133964413576584527

theorem tailTrace_3028535 : CollatzResearch.WordTrace tailWord_3028535 prefixEnd_3028535 1555094133964413576584527 := by
  unfold tailWord_3028535
  simp only [CollatzResearch.WordTrace]
  refine ⟨110459746083142402444119059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73639830722094934962746039 110459746083142402444119059)
  ·
    refine ⟨165689619124713603666178589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110459746083142402444119059 165689619124713603666178589)
    ·
      refine ⟨62133607171767601374816971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 165689619124713603666178589 62133607171767601374816971)
      ·
        refine ⟨93200410757651402062225457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62133607171767601374816971 93200410757651402062225457)
        ·
          refine ⟨69900308068238551546669093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93200410757651402062225457 69900308068238551546669093)
          ·
            refine ⟨13106307762794728415000455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 69900308068238551546669093 13106307762794728415000455)
            ·
              refine ⟨19659461644192092622500683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13106307762794728415000455 19659461644192092622500683)
              ·
                refine ⟨29489192466288138933751025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19659461644192092622500683 29489192466288138933751025)
                ·
                  refine ⟨22116894349716104200313269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29489192466288138933751025 22116894349716104200313269)
                  ·
                    refine ⟨2073458845285884768779369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 22116894349716104200313269 2073458845285884768779369)
                    ·
                      refine ⟨1555094133964413576584527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2073458845285884768779369 1555094133964413576584527)
                      ·
                        rfl

theorem cell23_3028535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 1, 1, 2, 5, 2].length) (baseStart_3028535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3028535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3028535 prefixEnd_3028535 := by exact prefixLift 3028535
  have htrace : WordTrace (prefixWord ++ tailWord_3028535) baseStart_3028535 baseEnd_3028535 := by
    simpa [prefixWord, tailWord_3028535, baseEnd_3028535] using wordTrace_append hprefix tailTrace_3028535
  have hstable : (prefixWord ++ tailWord_3028535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3028535).length < 2 ^ (prefixWord ++ tailWord_3028535).sum := by decide
  have hdescent : baseEnd_3028535 < baseStart_3028535 := by decide
  rcases family_descends (prefixWord ++ tailWord_3028535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3028538 : List Nat := [3, 1, 1, 1, 3, 2, 1, 3, 1, 2, 5]
def baseStart_3028538 : Nat := 118140960795 + 3028538 * 2 ^ 59
def prefixEnd_3028538 : Nat := 4983230072969 + 3 ^ 40 * 3028538 * 2
def baseEnd_3028538 : Nat := 1555095674406377064847013

theorem tailTrace_3028538 : CollatzResearch.WordTrace tailWord_3028538 prefixEnd_3028538 1555095674406377064847013 := by
  unfold tailWord_3028538
  simp only [CollatzResearch.WordTrace]
  refine ⟨27614963875532883489119567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73639903668087689304318845 27614963875532883489119567)
  ·
    refine ⟨41422445813299325233679351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27614963875532883489119567 41422445813299325233679351)
    ·
      refine ⟨62133668719948987850519027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41422445813299325233679351 62133668719948987850519027)
      ·
        refine ⟨93200503079923481775778541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62133668719948987850519027 93200503079923481775778541)
        ·
          refine ⟨34950188654971305665916953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 93200503079923481775778541 34950188654971305665916953)
          ·
            refine ⟨26212641491228479249437715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34950188654971305665916953 26212641491228479249437715)
            ·
              refine ⟨39318962236842718874156573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26212641491228479249437715 39318962236842718874156573)
              ·
                refine ⟨14744610838816019577808715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39318962236842718874156573 14744610838816019577808715)
                ·
                  refine ⟨22116916258224029366713073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14744610838816019577808715 22116916258224029366713073)
                  ·
                    refine ⟨16587687193668022025034805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22116916258224029366713073 16587687193668022025034805)
                    ·
                      refine ⟨1555095674406377064847013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16587687193668022025034805 1555095674406377064847013)
                      ·
                        rfl

theorem cell23_3028538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 3, 1, 2, 5].length) (baseStart_3028538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3028538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3028538 prefixEnd_3028538 := by exact prefixLift 3028538
  have htrace : WordTrace (prefixWord ++ tailWord_3028538) baseStart_3028538 baseEnd_3028538 := by
    simpa [prefixWord, tailWord_3028538, baseEnd_3028538] using wordTrace_append hprefix tailTrace_3028538
  have hstable : (prefixWord ++ tailWord_3028538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3028538).length < 2 ^ (prefixWord ++ tailWord_3028538).sum := by decide
  have hdescent : baseEnd_3028538 < baseStart_3028538 := by decide
  rcases family_descends (prefixWord ++ tailWord_3028538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3028562 : List Nat := [3, 2, 2, 1, 2, 4, 1, 1, 2, 5]
def baseStart_3028562 : Nat := 118140960795 + 3028562 * 2 ^ 59
def prefixEnd_3028562 : Nat := 4983230072969 + 3 ^ 40 * 3028562 * 2
def baseEnd_3028562 : Nat := 518369332647361656982301

theorem tailTrace_3028562 : CollatzResearch.WordTrace tailWord_3028562 prefixEnd_3028562 518369332647361656982301 := by
  unfold tailWord_3028562
  simp only [CollatzResearch.WordTrace]
  refine ⟨27615182713511146513837985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73640487236029724036901293 27615182713511146513837985)
  ·
    refine ⟨20711387035133359885378489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27615182713511146513837985 20711387035133359885378489)
    ·
      refine ⟨15533540276350019914033867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20711387035133359885378489 15533540276350019914033867)
      ·
        refine ⟨23300310414525029871050801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15533540276350019914033867 23300310414525029871050801)
        ·
          refine ⟨17475232810893772403288101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23300310414525029871050801 17475232810893772403288101)
          ·
            refine ⟨3276606152042582325616519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17475232810893772403288101 3276606152042582325616519)
            ·
              refine ⟨4914909228063873488424779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3276606152042582325616519 4914909228063873488424779)
              ·
                refine ⟨7372363842095810232637169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4914909228063873488424779 7372363842095810232637169)
                ·
                  refine ⟨5529272881571857674477877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7372363842095810232637169 5529272881571857674477877)
                  ·
                    refine ⟨518369332647361656982301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5529272881571857674477877 518369332647361656982301)
                    ·
                      rfl

theorem cell23_3028562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 4, 1, 1, 2, 5].length) (baseStart_3028562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3028562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3028562 prefixEnd_3028562 := by exact prefixLift 3028562
  have htrace : WordTrace (prefixWord ++ tailWord_3028562) baseStart_3028562 baseEnd_3028562 := by
    simpa [prefixWord, tailWord_3028562, baseEnd_3028562] using wordTrace_append hprefix tailTrace_3028562
  have hstable : (prefixWord ++ tailWord_3028562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3028562).length < 2 ^ (prefixWord ++ tailWord_3028562).sum := by decide
  have hdescent : baseEnd_3028562 < baseStart_3028562 := by decide
  rcases family_descends (prefixWord ++ tailWord_3028562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3028565 : List Nat := [1, 3, 2, 2, 1, 1, 1, 1, 3, 6, 2]
def baseStart_3028565 : Nat := 118140960795 + 3028565 * 2 ^ 59
def prefixEnd_3028565 : Nat := 4983230072969 + 3 ^ 40 * 3028565 * 2
def baseEnd_3028565 : Nat := 1555109538384048459209389

theorem tailTrace_3028565 : CollatzResearch.WordTrace tailWord_3028565 prefixEnd_3028565 1555109538384048459209389 := by
  unfold tailWord_3028565
  simp only [CollatzResearch.WordTrace]
  refine ⟨110460840273033717567711149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73640560182022478378474099 110460840273033717567711149)
  ·
    refine ⟨41422815102387644087891681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 110460840273033717567711149 41422815102387644087891681)
    ·
      refine ⟨31067111326790733065918761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41422815102387644087891681 31067111326790733065918761)
      ·
        refine ⟨23300333495093049799439071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31067111326790733065918761 23300333495093049799439071)
        ·
          refine ⟨34950500242639574699158607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23300333495093049799439071 34950500242639574699158607)
          ·
            refine ⟨52425750363959362048737911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34950500242639574699158607 52425750363959362048737911)
            ·
              refine ⟨78638625545939043073106867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52425750363959362048737911 78638625545939043073106867)
              ·
                refine ⟨117957938318908564609660301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 78638625545939043073106867 117957938318908564609660301)
                ·
                  refine ⟨44234226869590711728622613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 117957938318908564609660301 44234226869590711728622613)
                  ·
                    refine ⟨2073479384512064612279185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 44234226869590711728622613 2073479384512064612279185)
                    ·
                      refine ⟨1555109538384048459209389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2073479384512064612279185 1555109538384048459209389)
                      ·
                        rfl

theorem cell23_3028565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 1, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 1, 3, 6, 2].length) (baseStart_3028565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3028565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3028565 prefixEnd_3028565 := by exact prefixLift 3028565
  have htrace : WordTrace (prefixWord ++ tailWord_3028565) baseStart_3028565 baseEnd_3028565 := by
    simpa [prefixWord, tailWord_3028565, baseEnd_3028565] using wordTrace_append hprefix tailTrace_3028565
  have hstable : (prefixWord ++ tailWord_3028565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3028565).length < 2 ^ (prefixWord ++ tailWord_3028565).sum := by decide
  have hdescent : baseEnd_3028565 < baseStart_3028565 := by decide
  rcases family_descends (prefixWord ++ tailWord_3028565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3028585 : List Nat := [1, 2, 1, 1, 1, 4, 2, 4, 2, 2, 3]
def baseStart_3028585 : Nat := 118140960795 + 3028585 * 2 ^ 59
def prefixEnd_3028585 : Nat := 4983230072969 + 3 ^ 40 * 3028585 * 2
def baseEnd_3028585 : Nat := 1555119807997138380959297

theorem tailTrace_3028585 : CollatzResearch.WordTrace tailWord_3028585 prefixEnd_3028585 1555119807997138380959297 := by
  unfold tailWord_3028585
  simp only [CollatzResearch.WordTrace]
  refine ⟨110461569732961260983439209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73641046488640840655626139 110461569732961260983439209)
  ·
    refine ⟨82846177299720945737579407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110461569732961260983439209 82846177299720945737579407)
    ·
      refine ⟨124269265949581418606369111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82846177299720945737579407 124269265949581418606369111)
      ·
        refine ⟨186403898924372127909553667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124269265949581418606369111 186403898924372127909553667)
        ·
          refine ⟨279605848386558191864330501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 186403898924372127909553667 279605848386558191864330501)
          ·
            refine ⟨52426096572479660974561969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 279605848386558191864330501 52426096572479660974561969)
            ·
              refine ⟨39319572429359745730921477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52426096572479660974561969 39319572429359745730921477)
              ·
                refine ⟨7372419830504952324547777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39319572429359745730921477 7372419830504952324547777)
                ·
                  refine ⟨5529314872878714243410833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7372419830504952324547777 5529314872878714243410833)
                  ·
                    refine ⟨4146986154659035682558125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5529314872878714243410833 4146986154659035682558125)
                    ·
                      refine ⟨1555119807997138380959297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4146986154659035682558125 1555119807997138380959297)
                      ·
                        rfl

theorem cell23_3028585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 4, 2, 2, 3].length) (baseStart_3028585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3028585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3028585 prefixEnd_3028585 := by exact prefixLift 3028585
  have htrace : WordTrace (prefixWord ++ tailWord_3028585) baseStart_3028585 baseEnd_3028585 := by
    simpa [prefixWord, tailWord_3028585, baseEnd_3028585] using wordTrace_append hprefix tailTrace_3028585
  have hstable : (prefixWord ++ tailWord_3028585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3028585).length < 2 ^ (prefixWord ++ tailWord_3028585).sum := by decide
  have hdescent : baseEnd_3028585 < baseStart_3028585 := by decide
  rcases family_descends (prefixWord ++ tailWord_3028585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3028592 : List Nat := [2, 1, 1, 1, 6, 2, 2, 1, 3, 4]
def baseStart_3028592 : Nat := 118140960795 + 3028592 * 2 ^ 59
def prefixEnd_3028592 : Nat := 4983230072969 + 3 ^ 40 * 3028592 * 2
def baseEnd_3028592 : Nat := 518374467453906617857255

theorem tailTrace_3028592 : CollatzResearch.WordTrace tailWord_3028592 prefixEnd_3028592 518374467453906617857255 := by
  unfold tailWord_3028592
  simp only [CollatzResearch.WordTrace]
  refine ⟨55230912521967950589472015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73641216695957267452629353 55230912521967950589472015)
  ·
    refine ⟨82846368782951925884208023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55230912521967950589472015 82846368782951925884208023)
    ·
      refine ⟨124269553174427888826312035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82846368782951925884208023 124269553174427888826312035)
      ·
        refine ⟨186404329761641833239468053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124269553174427888826312035 186404329761641833239468053)
        ·
          refine ⟨8737702957576960933100065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 186404329761641833239468053 8737702957576960933100065)
          ·
            refine ⟨6553277218182720699825049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8737702957576960933100065 6553277218182720699825049)
            ·
              refine ⟨4914957913637040524868787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6553277218182720699825049 4914957913637040524868787)
              ·
                refine ⟨7372436870455560787303181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4914957913637040524868787 7372436870455560787303181)
                ·
                  refine ⟨2764663826420835295238693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7372436870455560787303181 2764663826420835295238693)
                  ·
                    refine ⟨518374467453906617857255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2764663826420835295238693 518374467453906617857255)
                    ·
                      rfl

theorem cell23_3028592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 2, 1, 3, 4].length) (baseStart_3028592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3028592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3028592 prefixEnd_3028592 := by exact prefixLift 3028592
  have htrace : WordTrace (prefixWord ++ tailWord_3028592) baseStart_3028592 baseEnd_3028592 := by
    simpa [prefixWord, tailWord_3028592, baseEnd_3028592] using wordTrace_append hprefix tailTrace_3028592
  have hstable : (prefixWord ++ tailWord_3028592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3028592).length < 2 ^ (prefixWord ++ tailWord_3028592).sum := by decide
  have hdescent : baseEnd_3028592 < baseStart_3028592 := by decide
  rcases family_descends (prefixWord ++ tailWord_3028592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3028608 : List Nat := [2, 1, 1, 2, 1, 4, 1, 2, 1, 2, 6]
def baseStart_3028608 : Nat := 118140960795 + 3028608 * 2 ^ 59
def prefixEnd_3028608 : Nat := 4983230072969 + 3 ^ 40 * 3028608 * 2
def baseEnd_3028608 : Nat := 1555131618052191790971691

theorem tailTrace_3028608 : CollatzResearch.WordTrace tailWord_3028608 prefixEnd_3028608 1555131618052191790971691 := by
  unfold tailWord_3028608
  simp only [CollatzResearch.WordTrace]
  refine ⟨55231204305938967955763239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73641605741251957274350985 55231204305938967955763239)
  ·
    refine ⟨82846806458908451933644859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55231204305938967955763239 82846806458908451933644859)
    ·
      refine ⟨124270209688362677900467289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82846806458908451933644859 124270209688362677900467289)
      ·
        refine ⟨93202657266272008425350467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 124270209688362677900467289 93202657266272008425350467)
        ·
          refine ⟨139803985899408012638025701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93202657266272008425350467 139803985899408012638025701)
          ·
            refine ⟨26213247356139002369629819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 139803985899408012638025701 26213247356139002369629819)
            ·
              refine ⟨39319871034208503554444729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26213247356139002369629819 39319871034208503554444729)
              ·
                refine ⟨29489903275656377665833547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39319871034208503554444729 29489903275656377665833547)
                ·
                  refine ⟨44234854913484566498750321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29489903275656377665833547 44234854913484566498750321)
                  ·
                    refine ⟨33176141185113424874062741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 44234854913484566498750321 33176141185113424874062741)
                    ·
                      refine ⟨1555131618052191790971691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 33176141185113424874062741 1555131618052191790971691)
                      ·
                        rfl

theorem cell23_3028608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 2, 1, 2, 6].length) (baseStart_3028608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3028608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3028608 prefixEnd_3028608 := by exact prefixLift 3028608
  have htrace : WordTrace (prefixWord ++ tailWord_3028608) baseStart_3028608 baseEnd_3028608 := by
    simpa [prefixWord, tailWord_3028608, baseEnd_3028608] using wordTrace_append hprefix tailTrace_3028608
  have hstable : (prefixWord ++ tailWord_3028608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3028608).length < 2 ^ (prefixWord ++ tailWord_3028608).sum := by decide
  have hdescent : baseEnd_3028608 < baseStart_3028608 := by decide
  rcases family_descends (prefixWord ++ tailWord_3028608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3028655 : List Nat := [1, 1, 2, 1, 2, 4, 2, 2, 3, 1, 4]
def baseStart_3028655 : Nat := 118140960795 + 3028655 * 2 ^ 59
def prefixEnd_3028655 : Nat := 4983230072969 + 3 ^ 40 * 3028655 * 2
def baseEnd_3028655 : Nat := 1555155751642953107083975

theorem tailTrace_3028655 : CollatzResearch.WordTrace tailWord_3028655 prefixEnd_3028655 1555155751642953107083975 := by
  unfold tailWord_3028655
  simp only [CollatzResearch.WordTrace]
  refine ⟨110464122842707662938487419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73642748561805108625658279 110464122842707662938487419)
  ·
    refine ⟨165696184264061494407731129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110464122842707662938487419 165696184264061494407731129)
    ·
      refine ⟨124272138198046120805798347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 165696184264061494407731129 124272138198046120805798347)
      ·
        refine ⟨186408207297069181208697521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124272138198046120805798347 186408207297069181208697521)
        ·
          refine ⟨139806155472801885906523141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 186408207297069181208697521 139806155472801885906523141)
          ·
            refine ⟨26213654151150353607473089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 139806155472801885906523141 26213654151150353607473089)
            ·
              refine ⟨19660240613362765205604817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26213654151150353607473089 19660240613362765205604817)
              ·
                refine ⟨14745180460022073904203613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19660240613362765205604817 14745180460022073904203613)
                ·
                  refine ⟨5529442672508277714076355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14745180460022073904203613 5529442672508277714076355)
                  ·
                    refine ⟨8294164008762416571114533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5529442672508277714076355 8294164008762416571114533)
                    ·
                      refine ⟨1555155751642953107083975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8294164008762416571114533 1555155751642953107083975)
                      ·
                        rfl

theorem cell23_3028655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 2, 2, 3, 1, 4].length) (baseStart_3028655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3028655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3028655 prefixEnd_3028655 := by exact prefixLift 3028655
  have htrace : WordTrace (prefixWord ++ tailWord_3028655) baseStart_3028655 baseEnd_3028655 := by
    simpa [prefixWord, tailWord_3028655, baseEnd_3028655] using wordTrace_append hprefix tailTrace_3028655
  have hstable : (prefixWord ++ tailWord_3028655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3028655).length < 2 ^ (prefixWord ++ tailWord_3028655).sum := by decide
  have hdescent : baseEnd_3028655 < baseStart_3028655 := by decide
  rcases family_descends (prefixWord ++ tailWord_3028655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3028682 : List Nat := [3, 1, 2, 1, 5, 1, 1, 2, 1, 6]
def baseStart_3028682 : Nat := 118140960795 + 3028682 * 2 ^ 59
def prefixEnd_3028682 : Nat := 4983230072969 + 3 ^ 40 * 3028682 * 2
def baseEnd_3028682 : Nat := 518389871873541500482117

theorem tailTrace_3028682 : CollatzResearch.WordTrace tailWord_3028682 prefixEnd_3028682 518389871873541500482117 := by
  unfold tailWord_3028682
  simp only [CollatzResearch.WordTrace]
  refine ⟨27616276903402461637430075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73643405075739897699813533 27616276903402461637430075)
  ·
    refine ⟨41424415355103692456145113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27616276903402461637430075 41424415355103692456145113)
    ·
      refine ⟨31068311516327769342108835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41424415355103692456145113 31068311516327769342108835)
      ·
        refine ⟨46602467274491654013163253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31068311516327769342108835 46602467274491654013163253)
        ·
          refine ⟨4368981306983592563734055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 46602467274491654013163253 4368981306983592563734055)
          ·
            refine ⟨6553471960475388845601083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4368981306983592563734055 6553471960475388845601083)
            ·
              refine ⟨9830207940713083268401625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6553471960475388845601083 9830207940713083268401625)
              ·
                refine ⟨7372655955534812451301219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9830207940713083268401625 7372655955534812451301219)
                ·
                  refine ⟨11058983933302218676951829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7372655955534812451301219 11058983933302218676951829)
                  ·
                    refine ⟨518389871873541500482117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11058983933302218676951829 518389871873541500482117)
                    ·
                      rfl

theorem cell23_3028682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 1, 2, 1, 6].length) (baseStart_3028682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3028682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3028682 prefixEnd_3028682 := by exact prefixLift 3028682
  have htrace : WordTrace (prefixWord ++ tailWord_3028682) baseStart_3028682 baseEnd_3028682 := by
    simpa [prefixWord, tailWord_3028682, baseEnd_3028682] using wordTrace_append hprefix tailTrace_3028682
  have hstable : (prefixWord ++ tailWord_3028682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3028682).length < 2 ^ (prefixWord ++ tailWord_3028682).sum := by decide
  have hdescent : baseEnd_3028682 < baseStart_3028682 := by decide
  rcases family_descends (prefixWord ++ tailWord_3028682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3028689 : List Nat := [1, 2, 2, 1, 2, 5, 3, 1, 1, 1, 4]
def baseStart_3028689 : Nat := 118140960795 + 3028689 * 2 ^ 59
def prefixEnd_3028689 : Nat := 4983230072969 + 3 ^ 40 * 3028689 * 2
def baseEnd_3028689 : Nat := 1555173209985205974058819

theorem tailTrace_3028689 : CollatzResearch.WordTrace tailWord_3028689 prefixEnd_3028689 1555173209985205974058819 := by
  unfold tailWord_3028689
  simp only [CollatzResearch.WordTrace]
  refine ⟨110465362924584486745225121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73643575283056324496816747 110465362924584486745225121)
  ·
    refine ⟨82849022193438365058918841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110465362924584486745225121 82849022193438365058918841)
    ·
      refine ⟨62136766645078773794189131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82849022193438365058918841 62136766645078773794189131)
      ·
        refine ⟨93205149967618160691283697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62136766645078773794189131 93205149967618160691283697)
        ·
          refine ⟨69903862475713620518462773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93205149967618160691283697 69903862475713620518462773)
          ·
            refine ⟨6553487107098151923605885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 69903862475713620518462773 6553487107098151923605885)
            ·
              refine ⟨2457557665161806971352207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6553487107098151923605885 2457557665161806971352207)
              ·
                refine ⟨3686336497742710457028311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2457557665161806971352207 3686336497742710457028311)
                ·
                  refine ⟨5529504746614065685542467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3686336497742710457028311 5529504746614065685542467)
                  ·
                    refine ⟨8294257119921098528313701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5529504746614065685542467 8294257119921098528313701)
                    ·
                      refine ⟨1555173209985205974058819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8294257119921098528313701 1555173209985205974058819)
                      ·
                        rfl

theorem cell23_3028689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 3, 1, 1, 1, 4].length) (baseStart_3028689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3028689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3028689 prefixEnd_3028689 := by exact prefixLift 3028689
  have htrace : WordTrace (prefixWord ++ tailWord_3028689) baseStart_3028689 baseEnd_3028689 := by
    simpa [prefixWord, tailWord_3028689, baseEnd_3028689] using wordTrace_append hprefix tailTrace_3028689
  have hstable : (prefixWord ++ tailWord_3028689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3028689).length < 2 ^ (prefixWord ++ tailWord_3028689).sum := by decide
  have hdescent : baseEnd_3028689 < baseStart_3028689 := by decide
  rcases family_descends (prefixWord ++ tailWord_3028689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3028712 : List Nat := [2, 1, 4, 1, 3, 3, 1, 8]
def baseStart_3028712 : Nat := 118140960795 + 3028712 * 2 ^ 59
def prefixEnd_3028712 : Nat := 4983230072969 + 3 ^ 40 * 3028712 * 2
def baseEnd_3028712 : Nat := 57599445186676273484119

theorem tailTrace_3028712 : CollatzResearch.WordTrace tailWord_3028712 prefixEnd_3028712 57599445186676273484119 := by
  unfold tailWord_3028712
  simp only [CollatzResearch.WordTrace]
  refine ⟨55233100901750580836656195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73644134535667441115541593 55233100901750580836656195)
  ·
    refine ⟨82849651352625871254984293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55233100901750580836656195 82849651352625871254984293)
    ·
      refine ⟨15534309628617350860309555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 82849651352625871254984293 15534309628617350860309555)
      ·
        refine ⟨23301464442926026290464333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15534309628617350860309555 23301464442926026290464333)
        ·
          refine ⟨8738049166097259858924125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23301464442926026290464333 8738049166097259858924125)
          ·
            refine ⟨3276768437286472447096547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8738049166097259858924125 3276768437286472447096547)
            ·
              refine ⟨4915152655929708670644821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3276768437286472447096547 4915152655929708670644821)
              ·
                refine ⟨57599445186676273484119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4915152655929708670644821 57599445186676273484119)
                ·
                  rfl

theorem cell23_3028712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 3, 1, 8].length) (baseStart_3028712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3028712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3028712 prefixEnd_3028712 := by exact prefixLift 3028712
  have htrace : WordTrace (prefixWord ++ tailWord_3028712) baseStart_3028712 baseEnd_3028712 := by
    simpa [prefixWord, tailWord_3028712, baseEnd_3028712] using wordTrace_append hprefix tailTrace_3028712
  have hstable : (prefixWord ++ tailWord_3028712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3028712).length < 2 ^ (prefixWord ++ tailWord_3028712).sum := by decide
  have hdescent : baseEnd_3028712 < baseStart_3028712 := by decide
  rcases family_descends (prefixWord ++ tailWord_3028712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3028743 : List Nat := [1, 1, 4, 4, 2, 2, 2, 1, 1, 2, 3]
def baseStart_3028743 : Nat := 118140960795 + 3028743 * 2 ^ 59
def prefixEnd_3028743 : Nat := 4983230072969 + 3 ^ 40 * 3028743 * 2
def baseEnd_3028743 : Nat := 1555200937940548762783571

theorem tailTrace_3028743 : CollatzResearch.WordTrace tailWord_3028743 prefixEnd_3028743 1555200937940548762783571 := by
  unfold tailWord_3028743
  simp only [CollatzResearch.WordTrace]
  refine ⟨110467332466388853967690883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73644888310925902645127255 110467332466388853967690883)
  ·
    refine ⟨165700998699583280951536325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110467332466388853967690883 165700998699583280951536325)
    ·
      refine ⟨31068937256171865178413061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 165700998699583280951536325 31068937256171865178413061)
      ·
        refine ⟨5825425735532224720952449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31068937256171865178413061 5825425735532224720952449)
        ·
          refine ⟨4369069301649168540714337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5825425735532224720952449 4369069301649168540714337)
          ·
            refine ⟨3276801976236876405535753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4369069301649168540714337 3276801976236876405535753)
            ·
              refine ⟨2457601482177657304151815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3276801976236876405535753 2457601482177657304151815)
              ·
                refine ⟨3686402223266485956227723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2457601482177657304151815 3686402223266485956227723)
                ·
                  refine ⟨5529603334899728934341585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3686402223266485956227723 5529603334899728934341585)
                  ·
                    refine ⟨4147202501174796700756189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5529603334899728934341585 4147202501174796700756189)
                    ·
                      refine ⟨1555200937940548762783571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4147202501174796700756189 1555200937940548762783571)
                      ·
                        rfl

theorem cell23_3028743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 2, 2, 1, 1, 2, 3].length) (baseStart_3028743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3028743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3028743 prefixEnd_3028743 := by exact prefixLift 3028743
  have htrace : WordTrace (prefixWord ++ tailWord_3028743) baseStart_3028743 baseEnd_3028743 := by
    simpa [prefixWord, tailWord_3028743, baseEnd_3028743] using wordTrace_append hprefix tailTrace_3028743
  have hstable : (prefixWord ++ tailWord_3028743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3028743).length < 2 ^ (prefixWord ++ tailWord_3028743).sum := by decide
  have hdescent : baseEnd_3028743 < baseStart_3028743 := by decide
  rcases family_descends (prefixWord ++ tailWord_3028743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3028772 : List Nat := [2, 3, 1, 3, 2, 1, 2, 1, 2, 6]
def baseStart_3028772 : Nat := 118140960795 + 3028772 * 2 ^ 59
def prefixEnd_3028772 : Nat := 4983230072969 + 3 ^ 40 * 3028772 * 2
def baseEnd_3028772 : Nat := 518405276293176383106979

theorem tailTrace_3028772 : CollatzResearch.WordTrace tailWord_3028772 prefixEnd_3028772 518405276293176383106979 := by
  unfold tailWord_3028772
  simp only [CollatzResearch.WordTrace]
  refine ⟨55234195091641895960248285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73645593455522527946997713 55234195091641895960248285)
  ·
    refine ⟨20712823159365710985093107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55234195091641895960248285 20712823159365710985093107)
    ·
      refine ⟨31069234739048566477639661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20712823159365710985093107 31069234739048566477639661)
      ·
        refine ⟨11650963027143212429114873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31069234739048566477639661 11650963027143212429114873)
        ·
          refine ⟨8738222270357409321836155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11650963027143212429114873 8738222270357409321836155)
          ·
            refine ⟨13107333405536113982754233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8738222270357409321836155 13107333405536113982754233)
            ·
              refine ⟨9830500054152085487065675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13107333405536113982754233 9830500054152085487065675)
              ·
                refine ⟨14745750081228128230598513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9830500054152085487065675 14745750081228128230598513)
                ·
                  refine ⟨11059312560921096172948885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14745750081228128230598513 11059312560921096172948885)
                  ·
                    refine ⟨518405276293176383106979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11059312560921096172948885 518405276293176383106979)
                    ·
                      rfl

theorem cell23_3028772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 2, 1, 2, 6].length) (baseStart_3028772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3028772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3028772 prefixEnd_3028772 := by exact prefixLift 3028772
  have htrace : WordTrace (prefixWord ++ tailWord_3028772) baseStart_3028772 baseEnd_3028772 := by
    simpa [prefixWord, tailWord_3028772, baseEnd_3028772] using wordTrace_append hprefix tailTrace_3028772
  have hstable : (prefixWord ++ tailWord_3028772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3028772).length < 2 ^ (prefixWord ++ tailWord_3028772).sum := by decide
  have hdescent : baseEnd_3028772 < baseStart_3028772 := by decide
  rcases family_descends (prefixWord ++ tailWord_3028772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3028813 : List Nat := [1, 6, 1, 2, 1, 1, 2, 1, 4, 2, 2]
def baseStart_3028813 : Nat := 118140960795 + 3028813 * 2 ^ 59
def prefixEnd_3028813 : Nat := 4983230072969 + 3 ^ 40 * 3028813 * 2
def baseEnd_3028813 : Nat := 1555236881586363488908249

theorem tailTrace_3028813 : CollatzResearch.WordTrace tailWord_3028813 prefixEnd_3028813 1555236881586363488908249 := by
  unfold tailWord_3028813
  simp only [CollatzResearch.WordTrace]
  refine ⟨110469885576135255922739093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73646590384090170615159395 110469885576135255922739093)
  ·
    refine ⟨5178275886381340121378395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 110469885576135255922739093 5178275886381340121378395)
    ·
      refine ⟨7767413829572010182067593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5178275886381340121378395 7767413829572010182067593)
      ·
        refine ⟨5825560372179007636550695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7767413829572010182067593 5825560372179007636550695)
        ·
          refine ⟨8738340558268511454826043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5825560372179007636550695 8738340558268511454826043)
          ·
            refine ⟨13107510837402767182239065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8738340558268511454826043 13107510837402767182239065)
            ·
              refine ⟨9830633128052075386679299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13107510837402767182239065 9830633128052075386679299)
              ·
                refine ⟨14745949692078113080018949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9830633128052075386679299 14745949692078113080018949)
                ·
                  refine ⟨2764865567264646202503553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14745949692078113080018949 2764865567264646202503553)
                  ·
                    refine ⟨2073649175448484651877665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2764865567264646202503553 2073649175448484651877665)
                    ·
                      refine ⟨1555236881586363488908249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2073649175448484651877665 1555236881586363488908249)
                      ·
                        rfl

theorem cell23_3028813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 2, 1, 4, 2, 2].length) (baseStart_3028813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3028813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3028813 prefixEnd_3028813 := by exact prefixLift 3028813
  have htrace : WordTrace (prefixWord ++ tailWord_3028813) baseStart_3028813 baseEnd_3028813 := by
    simpa [prefixWord, tailWord_3028813, baseEnd_3028813] using wordTrace_append hprefix tailTrace_3028813
  have hstable : (prefixWord ++ tailWord_3028813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3028813).length < 2 ^ (prefixWord ++ tailWord_3028813).sum := by decide
  have hdescent : baseEnd_3028813 < baseStart_3028813 := by decide
  rcases family_descends (prefixWord ++ tailWord_3028813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3028855 : List Nat := [1, 1, 3, 1, 1, 2, 1, 1, 1, 2, 9]
def baseStart_3028855 : Nat := 118140960795 + 3028855 * 2 ^ 59
def prefixEnd_3028855 : Nat := 4983230072969 + 3 ^ 40 * 3028855 * 2
def baseEnd_3028855 : Nat := 1555258447773852324583055

theorem tailTrace_3028855 : CollatzResearch.WordTrace tailWord_3028855 prefixEnd_3028855 1555258447773852324583055 := by
  unfold tailWord_3028855
  simp only [CollatzResearch.WordTrace]
  refine ⟨110471417441983097095768019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73647611627988731397178679 110471417441983097095768019)
  ·
    refine ⟨165707126162974645643652029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110471417441983097095768019 165707126162974645643652029)
    ·
      refine ⟨62140172311115492116369511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 165707126162974645643652029 62140172311115492116369511)
      ·
        refine ⟨93210258466673238174554267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62140172311115492116369511 93210258466673238174554267)
        ·
          refine ⟨139815387700009857261831401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93210258466673238174554267 139815387700009857261831401)
          ·
            refine ⟨104861540775007392946373551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 139815387700009857261831401 104861540775007392946373551)
            ·
              refine ⟨157292311162511089419560327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 104861540775007392946373551 157292311162511089419560327)
              ·
                refine ⟨235938466743766634129340491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 157292311162511089419560327 235938466743766634129340491)
                ·
                  refine ⟨353907700115649951194010737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 235938466743766634129340491 353907700115649951194010737)
                  ·
                    refine ⟨265430775086737463395508053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 353907700115649951194010737 265430775086737463395508053)
                    ·
                      refine ⟨1555258447773852324583055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 265430775086737463395508053 1555258447773852324583055)
                      ·
                        rfl

theorem cell23_3028855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 1, 1, 2, 9].length) (baseStart_3028855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3028855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3028855 prefixEnd_3028855 := by exact prefixLift 3028855
  have htrace : WordTrace (prefixWord ++ tailWord_3028855) baseStart_3028855 baseEnd_3028855 := by
    simpa [prefixWord, tailWord_3028855, baseEnd_3028855] using wordTrace_append hprefix tailTrace_3028855
  have hstable : (prefixWord ++ tailWord_3028855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3028855).length < 2 ^ (prefixWord ++ tailWord_3028855).sum := by decide
  have hdescent : baseEnd_3028855 < baseStart_3028855 := by decide
  rcases family_descends (prefixWord ++ tailWord_3028855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3028869 : List Nat := [1, 3, 1, 1, 3, 2, 2, 2, 2, 4, 2]
def baseStart_3028869 : Nat := 118140960795 + 3028869 * 2 ^ 59
def prefixEnd_3028869 : Nat := 4983230072969 + 3 ^ 40 * 3028869 * 2
def baseEnd_3028869 : Nat := 1555265636503015269807991

theorem tailTrace_3028869 : CollatzResearch.WordTrace tailWord_3028869 prefixEnd_3028869 1555265636503015269807991 := by
  unfold tailWord_3028869
  simp only [CollatzResearch.WordTrace]
  refine ⟨110471928063932377486777661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73647952042621584991185107 110471928063932377486777661)
  ·
    refine ⟨41426973023974641557541623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 110471928063932377486777661 41426973023974641557541623)
    ·
      refine ⟨62140459535961962336312435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41426973023974641557541623 62140459535961962336312435)
      ·
        refine ⟨93210689303942943504468653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62140459535961962336312435 93210689303942943504468653)
        ·
          refine ⟨34954008488978603814175745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 93210689303942943504468653 34954008488978603814175745)
          ·
            refine ⟨26215506366733952860631809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34954008488978603814175745 26215506366733952860631809)
            ·
              refine ⟨19661629775050464645473857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26215506366733952860631809 19661629775050464645473857)
              ·
                refine ⟨14746222331287848484105393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19661629775050464645473857 14746222331287848484105393)
                ·
                  refine ⟨11059666748465886363079045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14746222331287848484105393 11059666748465886363079045)
                  ·
                    refine ⟨2073687515337353693077321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11059666748465886363079045 2073687515337353693077321)
                    ·
                      refine ⟨1555265636503015269807991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2073687515337353693077321 1555265636503015269807991)
                      ·
                        rfl

theorem cell23_3028869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 2, 2, 2, 4, 2].length) (baseStart_3028869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3028869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3028869 prefixEnd_3028869 := by exact prefixLift 3028869
  have htrace : WordTrace (prefixWord ++ tailWord_3028869) baseStart_3028869 baseEnd_3028869 := by
    simpa [prefixWord, tailWord_3028869, baseEnd_3028869] using wordTrace_append hprefix tailTrace_3028869
  have hstable : (prefixWord ++ tailWord_3028869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3028869).length < 2 ^ (prefixWord ++ tailWord_3028869).sum := by decide
  have hdescent : baseEnd_3028869 < baseStart_3028869 := by decide
  rcases family_descends (prefixWord ++ tailWord_3028869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3028913 : List Nat := [1, 2, 2, 4, 2, 2, 2, 3, 1, 4]
def baseStart_3028913 : Nat := 118140960795 + 3028913 * 2 ^ 59
def prefixEnd_3028913 : Nat := 4983230072969 + 3 ^ 40 * 3028913 * 2
def baseEnd_3028913 : Nat := 518429409883937699219263

theorem tailTrace_3028913 : CollatzResearch.WordTrace tailWord_3028913 prefixEnd_3028913 518429409883937699219263 := by
  unfold tailWord_3028913
  simp only [CollatzResearch.WordTrace]
  refine ⟨110473532875772973001379393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73649021917181982000919595 110473532875772973001379393)
  ·
    refine ⟨82855149656829729751034545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110473532875772973001379393 82855149656829729751034545)
    ·
      refine ⟨62141362242622297313275909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82855149656829729751034545 62141362242622297313275909)
      ·
        refine ⟨11651505420491680746239233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 62141362242622297313275909 11651505420491680746239233)
        ·
          refine ⟨8738629065368760559679425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11651505420491680746239233 8738629065368760559679425)
          ·
            refine ⟨6553971799026570419759569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8738629065368760559679425 6553971799026570419759569)
            ·
              refine ⟨4915478849269927814819677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6553971799026570419759569 4915478849269927814819677)
              ·
                refine ⟨1843304568476222930557379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4915478849269927814819677 1843304568476222930557379)
                ·
                  refine ⟨2764956852714334395836069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1843304568476222930557379 2764956852714334395836069)
                  ·
                    refine ⟨518429409883937699219263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2764956852714334395836069 518429409883937699219263)
                    ·
                      rfl

theorem cell23_3028913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 2, 3, 1, 4].length) (baseStart_3028913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3028913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3028913 prefixEnd_3028913 := by exact prefixLift 3028913
  have htrace : WordTrace (prefixWord ++ tailWord_3028913) baseStart_3028913 baseEnd_3028913 := by
    simpa [prefixWord, tailWord_3028913, baseEnd_3028913] using wordTrace_append hprefix tailTrace_3028913
  have hstable : (prefixWord ++ tailWord_3028913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3028913).length < 2 ^ (prefixWord ++ tailWord_3028913).sum := by decide
  have hdescent : baseEnd_3028913 < baseStart_3028913 := by decide
  rcases family_descends (prefixWord ++ tailWord_3028913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3028919 : List Nat := [1, 1, 3, 1, 3, 1, 1, 1, 7, 1, 3]
def baseStart_3028919 : Nat := 118140960795 + 3028919 * 2 ^ 59
def prefixEnd_3028919 : Nat := 4983230072969 + 3 ^ 40 * 3028919 * 2
def baseEnd_3028919 : Nat := 1555291310535740074182761

theorem tailTrace_3028919 : CollatzResearch.WordTrace tailWord_3028919 prefixEnd_3028919 1555291310535740074182761 := by
  unfold tailWord_3028919
  simp only [CollatzResearch.WordTrace]
  refine ⟨110473751713751236026097811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73649167809167490684065207 110473751713751236026097811)
  ·
    refine ⟨165710627570626854039146717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110473751713751236026097811 165710627570626854039146717)
    ·
      refine ⟨62141485338985070264680019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 165710627570626854039146717 62141485338985070264680019)
      ·
        refine ⟨93212228008477605397020029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62141485338985070264680019 93212228008477605397020029)
        ·
          refine ⟨34954585503179102023882511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 93212228008477605397020029 34954585503179102023882511)
          ·
            refine ⟨52431878254768653035823767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34954585503179102023882511 52431878254768653035823767)
            ·
              refine ⟨78647817382152979553735651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52431878254768653035823767 78647817382152979553735651)
              ·
                refine ⟨117971726073229469330603477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 78647817382152979553735651 117971726073229469330603477)
                ·
                  refine ⟨2764962329841315687436019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 117971726073229469330603477 2764962329841315687436019)
                  ·
                    refine ⟨4147443494761973531154029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2764962329841315687436019 4147443494761973531154029)
                    ·
                      refine ⟨1555291310535740074182761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4147443494761973531154029 1555291310535740074182761)
                      ·
                        rfl

theorem cell23_3028919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 1, 7, 1, 3].length) (baseStart_3028919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3028919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3028919 prefixEnd_3028919 := by exact prefixLift 3028919
  have htrace : WordTrace (prefixWord ++ tailWord_3028919) baseStart_3028919 baseEnd_3028919 := by
    simpa [prefixWord, tailWord_3028919, baseEnd_3028919] using wordTrace_append hprefix tailTrace_3028919
  have hstable : (prefixWord ++ tailWord_3028919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3028919).length < 2 ^ (prefixWord ++ tailWord_3028919).sum := by decide
  have hdescent : baseEnd_3028919 < baseStart_3028919 := by decide
  rcases family_descends (prefixWord ++ tailWord_3028919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3028922 : List Nat := [3, 1, 1, 1, 2, 1, 2, 2, 5, 5]
def baseStart_3028922 : Nat := 118140960795 + 3028922 * 2 ^ 59
def prefixEnd_3028922 : Nat := 4983230072969 + 3 ^ 40 * 3028922 * 2
def baseEnd_3028922 : Nat := 518430950325901187481749

theorem tailTrace_3028922 : CollatzResearch.WordTrace tailWord_3028922 prefixEnd_3028922 518430950325901187481749 := by
  unfold tailWord_3028922
  simp only [CollatzResearch.WordTrace]
  refine ⟨27618465283185091884614255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73649240755160245025638013 27618465283185091884614255)
  ·
    refine ⟨41427697924777637826921383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27618465283185091884614255 41427697924777637826921383)
    ·
      refine ⟨62141546887166456740382075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41427697924777637826921383 62141546887166456740382075)
      ·
        refine ⟨93212320330749685110573113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62141546887166456740382075 93212320330749685110573113)
        ·
          refine ⟨69909240248062263832929835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93212320330749685110573113 69909240248062263832929835)
          ·
            refine ⟨104863860372093395749394753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69909240248062263832929835 104863860372093395749394753)
            ·
              refine ⟨78647895279070046812046065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 104863860372093395749394753 78647895279070046812046065)
              ·
                refine ⟨58985921459302535109034549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 78647895279070046812046065 58985921459302535109034549)
                ·
                  refine ⟨5529930136809612666471989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 58985921459302535109034549 5529930136809612666471989)
                  ·
                    refine ⟨518430950325901187481749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5529930136809612666471989 518430950325901187481749)
                    ·
                      rfl

theorem cell23_3028922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 2, 5, 5].length) (baseStart_3028922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3028922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3028922 prefixEnd_3028922 := by exact prefixLift 3028922
  have htrace : WordTrace (prefixWord ++ tailWord_3028922) baseStart_3028922 baseEnd_3028922 := by
    simpa [prefixWord, tailWord_3028922, baseEnd_3028922] using wordTrace_append hprefix tailTrace_3028922
  have hstable : (prefixWord ++ tailWord_3028922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3028922).length < 2 ^ (prefixWord ++ tailWord_3028922).sum := by decide
  have hdescent : baseEnd_3028922 < baseStart_3028922 := by decide
  rcases family_descends (prefixWord ++ tailWord_3028922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3028926 : List Nat := [4, 2, 1, 1, 1, 5, 1, 2, 6]
def baseStart_3028926 : Nat := 118140960795 + 3028926 * 2 ^ 59
def prefixEnd_3028926 : Nat := 4983230072969 + 3 ^ 40 * 3028926 * 2
def baseEnd_3028926 : Nat := 172810544988924616310581

theorem tailTrace_3028926 : CollatzResearch.WordTrace tailWord_3028926 prefixEnd_3028926 172810544988924616310581 := by
  unfold tailWord_3028926
  simp only [CollatzResearch.WordTrace]
  refine ⟨13809250878090734527700329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 73649338016483917481068421 13809250878090734527700329)
  ·
    refine ⟨10356938158568050895775247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13809250878090734527700329 10356938158568050895775247)
    ·
      refine ⟨15535407237852076343662871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10356938158568050895775247 15535407237852076343662871)
      ·
        refine ⟨23303110856778114515494307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15535407237852076343662871 23303110856778114515494307)
        ·
          refine ⟨34954666285167171773241461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23303110856778114515494307 34954666285167171773241461)
          ·
            refine ⟨3276999964234422353741387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 34954666285167171773241461 3276999964234422353741387)
            ·
              refine ⟨4915499946351633530612081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3276999964234422353741387 4915499946351633530612081)
              ·
                refine ⟨3686624959763725147959061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4915499946351633530612081 3686624959763725147959061)
                ·
                  refine ⟨172810544988924616310581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3686624959763725147959061 172810544988924616310581)
                  ·
                    rfl

theorem cell23_3028926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 5, 1, 2, 6].length) (baseStart_3028926 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3028926 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3028926 prefixEnd_3028926 := by exact prefixLift 3028926
  have htrace : WordTrace (prefixWord ++ tailWord_3028926) baseStart_3028926 baseEnd_3028926 := by
    simpa [prefixWord, tailWord_3028926, baseEnd_3028926] using wordTrace_append hprefix tailTrace_3028926
  have hstable : (prefixWord ++ tailWord_3028926).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3028926).length < 2 ^ (prefixWord ++ tailWord_3028926).sum := by decide
  have hdescent : baseEnd_3028926 < baseStart_3028926 := by decide
  rcases family_descends (prefixWord ++ tailWord_3028926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3028936 : List Nat := [2, 1, 3, 1, 4, 1, 1, 3, 3, 1, 3]
def baseStart_3028936 : Nat := 118140960795 + 3028936 * 2 ^ 59
def prefixEnd_3028936 : Nat := 4983230072969 + 3 ^ 40 * 3028936 * 2
def baseEnd_3028936 : Nat := 1555300039706866507670183

theorem tailTrace_3028936 : CollatzResearch.WordTrace tailWord_3028936 prefixEnd_3028936 1555300039706866507670183 := by
  unfold tailWord_3028936
  simp only [CollatzResearch.WordTrace]
  refine ⟨55237185877344823964733331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73649581169793098619644441 55237185877344823964733331)
  ·
    refine ⟨82855778816017235947099997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55237185877344823964733331 82855778816017235947099997)
    ·
      refine ⟨31070917056006463480162499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82855778816017235947099997 31070917056006463480162499)
      ·
        refine ⟨46606375584009695220243749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31070917056006463480162499 46606375584009695220243749)
        ·
          refine ⟨8738695422001817853795703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 46606375584009695220243749 8738695422001817853795703)
          ·
            refine ⟨13108043133002726780693555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8738695422001817853795703 13108043133002726780693555)
            ·
              refine ⟨19662064699504090171040333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13108043133002726780693555 19662064699504090171040333)
              ·
                refine ⟨7373274262314033814140125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19662064699504090171040333 7373274262314033814140125)
                ·
                  refine ⟨2764977848367762680302547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7373274262314033814140125 2764977848367762680302547)
                  ·
                    refine ⟨4147466772551644020453821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2764977848367762680302547 4147466772551644020453821)
                    ·
                      refine ⟨1555300039706866507670183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4147466772551644020453821 1555300039706866507670183)
                      ·
                        rfl

theorem cell23_3028936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 1, 3, 3, 1, 3].length) (baseStart_3028936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3028936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3028936 prefixEnd_3028936 := by exact prefixLift 3028936
  have htrace : WordTrace (prefixWord ++ tailWord_3028936) baseStart_3028936 baseEnd_3028936 := by
    simpa [prefixWord, tailWord_3028936, baseEnd_3028936] using wordTrace_append hprefix tailTrace_3028936
  have hstable : (prefixWord ++ tailWord_3028936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3028936).length < 2 ^ (prefixWord ++ tailWord_3028936).sum := by decide
  have hdescent : baseEnd_3028936 < baseStart_3028936 := by decide
  rcases family_descends (prefixWord ++ tailWord_3028936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3028976 : List Nat := [2, 1, 1, 1, 3, 2, 2, 2, 5, 2, 2]
def baseStart_3028976 : Nat := 118140960795 + 3028976 * 2 ^ 59
def prefixEnd_3028976 : Nat := 4983230072969 + 3 ^ 40 * 3028976 * 2
def baseEnd_3028976 : Nat := 1555320578933046351169999

theorem tailTrace_3028976 : CollatzResearch.WordTrace tailWord_3028976 prefixEnd_3028976 1555320578933046351169999 := by
  unfold tailWord_3028976
  simp only [CollatzResearch.WordTrace]
  refine ⟨55237915337272367380461391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73650553783029823173948521 55237915337272367380461391)
  ·
    refine ⟨82856873005908551070692087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55237915337272367380461391 82856873005908551070692087)
    ·
      refine ⟨124285309508862826606038131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82856873005908551070692087 124285309508862826606038131)
      ·
        refine ⟨186427964263294239909057197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124285309508862826606038131 186427964263294239909057197)
        ·
          refine ⟨69910486598735339965896449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 186427964263294239909057197 69910486598735339965896449)
          ·
            refine ⟨52432864949051504974422337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69910486598735339965896449 52432864949051504974422337)
            ·
              refine ⟨39324648711788628730816753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52432864949051504974422337 39324648711788628730816753)
              ·
                refine ⟨29493486533841471548112565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39324648711788628730816753 29493486533841471548112565)
                ·
                  refine ⟨2765014362547637957635553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 29493486533841471548112565 2765014362547637957635553)
                  ·
                    refine ⟨2073760771910728468226665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2765014362547637957635553 2073760771910728468226665)
                    ·
                      refine ⟨1555320578933046351169999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2073760771910728468226665 1555320578933046351169999)
                      ·
                        rfl

theorem cell23_3028976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 2, 5, 2, 2].length) (baseStart_3028976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3028976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3028976 prefixEnd_3028976 := by exact prefixLift 3028976
  have htrace : WordTrace (prefixWord ++ tailWord_3028976) baseStart_3028976 baseEnd_3028976 := by
    simpa [prefixWord, tailWord_3028976, baseEnd_3028976] using wordTrace_append hprefix tailTrace_3028976
  have hstable : (prefixWord ++ tailWord_3028976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3028976).length < 2 ^ (prefixWord ++ tailWord_3028976).sum := by decide
  have hdescent : baseEnd_3028976 < baseStart_3028976 := by decide
  rcases family_descends (prefixWord ++ tailWord_3028976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3028999 : List Nat := [1, 1, 4, 3, 1, 3, 2, 8]
def baseStart_3028999 : Nat := 118140960795 + 3028999 * 2 ^ 59
def prefixEnd_3028999 : Nat := 4983230072969 + 3 ^ 40 * 3028999 * 2
def baseEnd_3028999 : Nat := 57604903295855546710459

theorem tailTrace_3028999 : CollatzResearch.WordTrace tailWord_3028999 prefixEnd_3028999 57604903295855546710459 := by
  unfold tailWord_3028999
  simp only [CollatzResearch.WordTrace]
  refine ⟨110476669553461409689010051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73651113035640939792673367 110476669553461409689010051)
  ·
    refine ⟨165715004330192114533515077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110476669553461409689010051 165715004330192114533515077)
    ·
      refine ⟨31071563311911021475034077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 165715004330192114533515077 31071563311911021475034077)
      ·
        refine ⟨11651836241966633053137779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31071563311911021475034077 11651836241966633053137779)
        ·
          refine ⟨17477754362949949579706669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11651836241966633053137779 17477754362949949579706669)
          ·
            refine ⟨6554157886106231092390001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17477754362949949579706669 6554157886106231092390001)
            ·
              refine ⟨4915618414579673319292501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6554157886106231092390001 4915618414579673319292501)
              ·
                refine ⟨57604903295855546710459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4915618414579673319292501 57604903295855546710459)
                ·
                  rfl

theorem cell23_3028999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 2, 8].length) (baseStart_3028999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3028999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3028999 prefixEnd_3028999 := by exact prefixLift 3028999
  have htrace : WordTrace (prefixWord ++ tailWord_3028999) baseStart_3028999 baseEnd_3028999 := by
    simpa [prefixWord, tailWord_3028999, baseEnd_3028999] using wordTrace_append hprefix tailTrace_3028999
  have hstable : (prefixWord ++ tailWord_3028999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3028999).length < 2 ^ (prefixWord ++ tailWord_3028999).sum := by decide
  have hdescent : baseEnd_3028999 < baseStart_3028999 := by decide
  rcases family_descends (prefixWord ++ tailWord_3028999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3029026 : List Nat := [3, 3, 1, 1, 1, 2, 3, 2, 1, 3, 3]
def baseStart_3029026 : Nat := 118140960795 + 3029026 * 2 ^ 59
def prefixEnd_3029026 : Nat := 4983230072969 + 3 ^ 40 * 3029026 * 2
def baseEnd_3029026 : Nat := 1555346252965771155544769

theorem tailTrace_3029026 : CollatzResearch.WordTrace tailWord_3029026 prefixEnd_3029026 1555346252965771155544769 := by
  unfold tailWord_3029026
  simp only [CollatzResearch.WordTrace]
  refine ⟨27619413581090898325060733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73651769549575728866828621 27619413581090898325060733)
  ·
    refine ⟨10357280092909086871897775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27619413581090898325060733 10357280092909086871897775)
    ·
      refine ⟨15535920139363630307846663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10357280092909086871897775 15535920139363630307846663)
      ·
        refine ⟨23303880209045445461769995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15535920139363630307846663 23303880209045445461769995)
        ·
          refine ⟨34955820313568168192654993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23303880209045445461769995 34955820313568168192654993)
          ·
            refine ⟨26216865235176126144491245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34955820313568168192654993 26216865235176126144491245)
            ·
              refine ⟨9831324463191047304184217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26216865235176126144491245 9831324463191047304184217)
              ·
                refine ⟨7373493347393285478138163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9831324463191047304184217 7373493347393285478138163)
                ·
                  refine ⟨11060240021089928217207245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7373493347393285478138163 11060240021089928217207245)
                  ·
                    refine ⟨4147590007908723081452717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11060240021089928217207245 4147590007908723081452717)
                    ·
                      refine ⟨1555346252965771155544769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4147590007908723081452717 1555346252965771155544769)
                      ·
                        rfl

theorem cell23_3029026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 3, 2, 1, 3, 3].length) (baseStart_3029026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3029026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3029026 prefixEnd_3029026 := by exact prefixLift 3029026
  have htrace : WordTrace (prefixWord ++ tailWord_3029026) baseStart_3029026 baseEnd_3029026 := by
    simpa [prefixWord, tailWord_3029026, baseEnd_3029026] using wordTrace_append hprefix tailTrace_3029026
  have hstable : (prefixWord ++ tailWord_3029026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3029026).length < 2 ^ (prefixWord ++ tailWord_3029026).sum := by decide
  have hdescent : baseEnd_3029026 < baseStart_3029026 := by decide
  rcases family_descends (prefixWord ++ tailWord_3029026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3029044 : List Nat := [2, 5, 1, 2, 2, 1, 1, 4, 1, 2, 2]
def baseStart_3029044 : Nat := 118140960795 + 3029044 * 2 ^ 59
def prefixEnd_3029044 : Nat := 4983230072969 + 3 ^ 40 * 3029044 * 2
def baseEnd_3029044 : Nat := 1555355495617552085119687

theorem tailTrace_3029044 : CollatzResearch.WordTrace tailWord_3029044 prefixEnd_3029044 1555355495617552085119687 := by
  unfold tailWord_3029044
  simp only [CollatzResearch.WordTrace]
  refine ⟨55239155419149191187199093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73652207225532254916265457 55239155419149191187199093)
  ·
    refine ⟨5178670820545236673799915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 55239155419149191187199093 5178670820545236673799915)
    ·
      refine ⟨7768006230817855010699873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5178670820545236673799915 7768006230817855010699873)
      ·
        refine ⟨5826004673113391258024905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7768006230817855010699873 5826004673113391258024905)
        ·
          refine ⟨4369503504835043443518679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5826004673113391258024905 4369503504835043443518679)
          ·
            refine ⟨6554255257252565165278019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4369503504835043443518679 6554255257252565165278019)
            ·
              refine ⟨9831382885878847747917029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6554255257252565165278019 9831382885878847747917029)
              ·
                refine ⟨1843384291102283952734443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9831382885878847747917029 1843384291102283952734443)
                ·
                  refine ⟨2765076436653425929101665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1843384291102283952734443 2765076436653425929101665)
                  ·
                    refine ⟨2073807327490069446826249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2765076436653425929101665 2073807327490069446826249)
                    ·
                      refine ⟨1555355495617552085119687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2073807327490069446826249 1555355495617552085119687)
                      ·
                        rfl

theorem cell23_3029044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 1, 4, 1, 2, 2].length) (baseStart_3029044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3029044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3029044 prefixEnd_3029044 := by exact prefixLift 3029044
  have htrace : WordTrace (prefixWord ++ tailWord_3029044) baseStart_3029044 baseEnd_3029044 := by
    simpa [prefixWord, tailWord_3029044, baseEnd_3029044] using wordTrace_append hprefix tailTrace_3029044
  have hstable : (prefixWord ++ tailWord_3029044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3029044).length < 2 ^ (prefixWord ++ tailWord_3029044).sum := by decide
  have hdescent : baseEnd_3029044 < baseStart_3029044 := by decide
  rcases family_descends (prefixWord ++ tailWord_3029044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3029100 : List Nat := [2, 2, 1, 1, 3, 3, 3, 2, 2, 2, 2]
def baseStart_3029100 : Nat := 118140960795 + 3029100 * 2 ^ 59
def prefixEnd_3029100 : Nat := 4983230072969 + 3 ^ 40 * 3029100 * 2
def baseEnd_3029100 : Nat := 1555384250534203866019429

theorem tailTrace_3029100 : CollatzResearch.WordTrace tailWord_3029100 prefixEnd_3029100 1555384250534203866019429 := by
  unfold tailWord_3029100
  simp only [CollatzResearch.WordTrace]
  refine ⟨55240176663047751969218377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73653568884063669292291169 55240176663047751969218377)
  ·
    refine ⟨41430132497285813976913783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55240176663047751969218377 41430132497285813976913783)
    ·
      refine ⟨62145198745928720965370675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41430132497285813976913783 62145198745928720965370675)
      ·
        refine ⟨93217798118893081448056013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62145198745928720965370675 93217798118893081448056013)
        ·
          refine ⟨34956674294584905543021005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 93217798118893081448056013 34956674294584905543021005)
          ·
            refine ⟨13108752860469339578632877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34956674294584905543021005 13108752860469339578632877)
            ·
              refine ⟨4915782322676002341987329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13108752860469339578632877 4915782322676002341987329)
              ·
                refine ⟨3686836742007001756490497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4915782322676002341987329 3686836742007001756490497)
                ·
                  refine ⟨2765127556505251317367873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3686836742007001756490497 2765127556505251317367873)
                  ·
                    refine ⟨2073845667378938488025905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2765127556505251317367873 2073845667378938488025905)
                    ·
                      refine ⟨1555384250534203866019429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2073845667378938488025905 1555384250534203866019429)
                      ·
                        rfl

theorem cell23_3029100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 2, 2, 2].length) (baseStart_3029100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3029100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3029100 prefixEnd_3029100 := by exact prefixLift 3029100
  have htrace : WordTrace (prefixWord ++ tailWord_3029100) baseStart_3029100 baseEnd_3029100 := by
    simpa [prefixWord, tailWord_3029100, baseEnd_3029100] using wordTrace_append hprefix tailTrace_3029100
  have hstable : (prefixWord ++ tailWord_3029100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3029100).length < 2 ^ (prefixWord ++ tailWord_3029100).sum := by decide
  have hdescent : baseEnd_3029100 < baseStart_3029100 := by decide
  rcases family_descends (prefixWord ++ tailWord_3029100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3029106 : List Nat := [3, 2, 1, 2, 2, 3, 2, 1, 7]
def baseStart_3029106 : Nat := 118140960795 + 3029106 * 2 ^ 59
def prefixEnd_3029106 : Nat := 4983230072969 + 3 ^ 40 * 3029106 * 2
def baseEnd_3029106 : Nat := 172820814602014538060489

theorem tailTrace_3029106 : CollatzResearch.WordTrace tailWord_3029106 prefixEnd_3029106 172820814602014538060489 := by
  unfold tailWord_3029106
  simp only [CollatzResearch.WordTrace]
  refine ⟨27620143041018441740788793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73653714776049177975436781 27620143041018441740788793)
  ·
    refine ⟨20715107280763831305591595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27620143041018441740788793 20715107280763831305591595)
    ·
      refine ⟨31072660921145746958387393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20715107280763831305591595 31072660921145746958387393)
      ·
        refine ⟨23304495690859310218790545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31072660921145746958387393 23304495690859310218790545)
        ·
          refine ⟨17478371768144482664092909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23304495690859310218790545 17478371768144482664092909)
          ·
            refine ⟨6554389413054180999034841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17478371768144482664092909 6554389413054180999034841)
            ·
              refine ⟨4915792059790635749276131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6554389413054180999034841 4915792059790635749276131)
              ·
                refine ⟨7373688089685953623914197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4915792059790635749276131 7373688089685953623914197)
                ·
                  refine ⟨172820814602014538060489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7373688089685953623914197 172820814602014538060489)
                  ·
                    rfl

theorem cell23_3029106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 2, 1, 7].length) (baseStart_3029106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3029106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3029106 prefixEnd_3029106 := by exact prefixLift 3029106
  have htrace : WordTrace (prefixWord ++ tailWord_3029106) baseStart_3029106 baseEnd_3029106 := by
    simpa [prefixWord, tailWord_3029106, baseEnd_3029106] using wordTrace_append hprefix tailTrace_3029106
  have hstable : (prefixWord ++ tailWord_3029106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3029106).length < 2 ^ (prefixWord ++ tailWord_3029106).sum := by decide
  have hdescent : baseEnd_3029106 < baseStart_3029106 := by decide
  rcases family_descends (prefixWord ++ tailWord_3029106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3029116 : List Nat := [2, 2, 2, 1, 1, 4, 2, 1, 2, 3, 3]
def baseStart_3029116 : Nat := 118140960795 + 3029116 * 2 ^ 59
def prefixEnd_3029116 : Nat := 4983230072969 + 3 ^ 40 * 3029116 * 2
def baseEnd_3029116 : Nat := 1555392466224675803419355

theorem tailTrace_3029116 : CollatzResearch.WordTrace tailWord_3029116 prefixEnd_3029116 1555392466224675803419355 := by
  unfold tailWord_3029116
  simp only [CollatzResearch.WordTrace]
  refine ⟨55240468447018769335509601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73653957929358359114012801 55240468447018769335509601)
  ·
    refine ⟨41430351335264077001632201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55240468447018769335509601 41430351335264077001632201)
    ·
      refine ⟨31072763501448057751224151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41430351335264077001632201 31072763501448057751224151)
      ·
        refine ⟨46609145252172086626836227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31072763501448057751224151 46609145252172086626836227)
        ·
          refine ⟨69913717878258129940254341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46609145252172086626836227 69913717878258129940254341)
          ·
            refine ⟨13108822102173399363797689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 69913717878258129940254341 13108822102173399363797689)
            ·
              refine ⟨9831616576630049522848267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13108822102173399363797689 9831616576630049522848267)
              ·
                refine ⟨14747424864945074284272401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9831616576630049522848267 14747424864945074284272401)
                ·
                  refine ⟨11060568648708805713204301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14747424864945074284272401 11060568648708805713204301)
                  ·
                    refine ⟨4147713243265802142451613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11060568648708805713204301 4147713243265802142451613)
                    ·
                      refine ⟨1555392466224675803419355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4147713243265802142451613 1555392466224675803419355)
                      ·
                        rfl

theorem cell23_3029116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 2, 1, 2, 3, 3].length) (baseStart_3029116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3029116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3029116 prefixEnd_3029116 := by exact prefixLift 3029116
  have htrace : WordTrace (prefixWord ++ tailWord_3029116) baseStart_3029116 baseEnd_3029116 := by
    simpa [prefixWord, tailWord_3029116, baseEnd_3029116] using wordTrace_append hprefix tailTrace_3029116
  have hstable : (prefixWord ++ tailWord_3029116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3029116).length < 2 ^ (prefixWord ++ tailWord_3029116).sum := by decide
  have hdescent : baseEnd_3029116 < baseStart_3029116 := by decide
  rcases family_descends (prefixWord ++ tailWord_3029116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3029117 : List Nat := [1, 4, 1, 1, 3, 3, 3, 1, 2, 2, 2]
def baseStart_3029117 : Nat := 118140960795 + 3029117 * 2 ^ 59
def prefixEnd_3029117 : Nat := 4983230072969 + 3 ^ 40 * 3029117 * 2
def baseEnd_3029117 : Nat := 1555392979705330299506851

theorem tailTrace_3029117 : CollatzResearch.WordTrace tailWord_3029117 prefixEnd_3029117 1555392979705330299506851 := by
  unfold tailWord_3029117
  simp only [CollatzResearch.WordTrace]
  refine ⟨110480973367033915841805605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73653982244689277227870403 110480973367033915841805605)
  ·
    refine ⟨20715182506318859220338551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 110480973367033915841805605 20715182506318859220338551)
    ·
      refine ⟨31072773759478288830507827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20715182506318859220338551 31072773759478288830507827)
      ·
        refine ⟨46609160639217433245761741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31072773759478288830507827 46609160639217433245761741)
        ·
          refine ⟨17478435239706537467160653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46609160639217433245761741 17478435239706537467160653)
          ·
            refine ⟨6554413214889951550185245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17478435239706537467160653 6554413214889951550185245)
            ·
              refine ⟨2457904955583731831319467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6554413214889951550185245 2457904955583731831319467)
              ·
                refine ⟨3686857433375597746979201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2457904955583731831319467 3686857433375597746979201)
                ·
                  refine ⟨2765143075031698310234401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3686857433375597746979201 2765143075031698310234401)
                  ·
                    refine ⟨2073857306273773732675801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2765143075031698310234401 2073857306273773732675801)
                    ·
                      refine ⟨1555392979705330299506851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2073857306273773732675801 1555392979705330299506851)
                      ·
                        rfl

theorem cell23_3029117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 3, 1, 2, 2, 2].length) (baseStart_3029117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3029117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3029117 prefixEnd_3029117 := by exact prefixLift 3029117
  have htrace : WordTrace (prefixWord ++ tailWord_3029117) baseStart_3029117 baseEnd_3029117 := by
    simpa [prefixWord, tailWord_3029117, baseEnd_3029117] using wordTrace_append hprefix tailTrace_3029117
  have hstable : (prefixWord ++ tailWord_3029117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3029117).length < 2 ^ (prefixWord ++ tailWord_3029117).sum := by decide
  have hdescent : baseEnd_3029117 < baseStart_3029117 := by decide
  rcases family_descends (prefixWord ++ tailWord_3029117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3029176 : List Nat := [2, 1, 2, 1, 2, 1, 3, 2, 4, 2, 3]
def baseStart_3029176 : Nat := 118140960795 + 3029176 * 2 ^ 59
def prefixEnd_3029176 : Nat := 4983230072969 + 3 ^ 40 * 3029176 * 2
def baseEnd_3029176 : Nat := 1555423275063945568669079

theorem tailTrace_3029176 : CollatzResearch.WordTrace tailWord_3029176 prefixEnd_3029176 1555423275063945568669079 := by
  unfold tailWord_3029176
  simp only [CollatzResearch.WordTrace]
  refine ⟨55241562636910084459101691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73655416849213445945468921 55241562636910084459101691)
  ·
    refine ⟨82862343955365126688652537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55241562636910084459101691 82862343955365126688652537)
    ·
      refine ⟨62146757966523845016489403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82862343955365126688652537 62146757966523845016489403)
      ·
        refine ⟨93220136949785767524734105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62146757966523845016489403 93220136949785767524734105)
        ·
          refine ⟨69915102712339325643550579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93220136949785767524734105 69915102712339325643550579)
          ·
            refine ⟨104872654068508988465325869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69915102712339325643550579 104872654068508988465325869)
            ·
              refine ⟨39327245275690870674497201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 104872654068508988465325869 39327245275690870674497201)
              ·
                refine ⟨29495433956768153005872901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39327245275690870674497201 29495433956768153005872901)
                ·
                  refine ⟨5530393866894028688601169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29495433956768153005872901 5530393866894028688601169)
                  ·
                    refine ⟨4147795400170521516450877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5530393866894028688601169 4147795400170521516450877)
                    ·
                      refine ⟨1555423275063945568669079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4147795400170521516450877 1555423275063945568669079)
                      ·
                        rfl

theorem cell23_3029176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 2, 4, 2, 3].length) (baseStart_3029176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3029176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3029176 prefixEnd_3029176 := by exact prefixLift 3029176
  have htrace : WordTrace (prefixWord ++ tailWord_3029176) baseStart_3029176 baseEnd_3029176 := by
    simpa [prefixWord, tailWord_3029176, baseEnd_3029176] using wordTrace_append hprefix tailTrace_3029176
  have hstable : (prefixWord ++ tailWord_3029176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3029176).length < 2 ^ (prefixWord ++ tailWord_3029176).sum := by decide
  have hdescent : baseEnd_3029176 < baseStart_3029176 := by decide
  rcases family_descends (prefixWord ++ tailWord_3029176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3029213 : List Nat := [1, 4, 3, 2, 1, 1, 1, 4, 6]
def baseStart_3029213 : Nat := 118140960795 + 3029213 * 2 ^ 59
def prefixEnd_3029213 : Nat := 4983230072969 + 3 ^ 40 * 3029213 * 2
def baseEnd_3029213 : Nat := 172826919316462435989601

theorem tailTrace_3029213 : CollatzResearch.WordTrace tailWord_3029213 prefixEnd_3029213 172826919316462435989601 := by
  unfold tailWord_3029213
  simp only [CollatzResearch.WordTrace]
  refine ⟨110484474774686124237300293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73656316516457416158200195 110484474774686124237300293)
  ·
    refine ⟨20715839020253648294493805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 110484474774686124237300293 20715839020253648294493805)
    ·
      refine ⟨7768439632595118110435177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20715839020253648294493805 7768439632595118110435177)
      ·
        refine ⟨5826329724446338582826383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7768439632595118110435177 5826329724446338582826383)
        ·
          refine ⟨8739494586669507874239575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5826329724446338582826383 8739494586669507874239575)
          ·
            refine ⟨13109241880004261811359363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8739494586669507874239575 13109241880004261811359363)
            ·
              refine ⟨19663862820006392717039045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13109241880004261811359363 19663862820006392717039045)
              ·
                refine ⟨3686974278751198634444821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19663862820006392717039045 3686974278751198634444821)
                ·
                  refine ⟨172826919316462435989601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3686974278751198634444821 172826919316462435989601)
                  ·
                    rfl

theorem cell23_3029213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 1, 4, 6].length) (baseStart_3029213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3029213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3029213 prefixEnd_3029213 := by exact prefixLift 3029213
  have htrace : WordTrace (prefixWord ++ tailWord_3029213) baseStart_3029213 baseEnd_3029213 := by
    simpa [prefixWord, tailWord_3029213, baseEnd_3029213] using wordTrace_append hprefix tailTrace_3029213
  have hstable : (prefixWord ++ tailWord_3029213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3029213).length < 2 ^ (prefixWord ++ tailWord_3029213).sum := by decide
  have hdescent : baseEnd_3029213 < baseStart_3029213 := by decide
  rcases family_descends (prefixWord ++ tailWord_3029213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3029226 : List Nat := [3, 1, 3, 1, 1, 2, 1, 1, 5, 5]
def baseStart_3029226 : Nat := 118140960795 + 3029226 * 2 ^ 59
def prefixEnd_3029226 : Nat := 4983230072969 + 3 ^ 40 * 3029226 * 2
def baseEnd_3029226 : Nat := 518482983032223457681283

theorem tailTrace_3029226 : CollatzResearch.WordTrace tailWord_3029226 prefixEnd_3029226 518482983032223457681283 := by
  unfold tailWord_3029226
  simp only [CollatzResearch.WordTrace]
  refine ⟨27621237230909756864380883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73656632615759351638349021 27621237230909756864380883)
  ·
    refine ⟨41431855846364635296571325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27621237230909756864380883 41431855846364635296571325)
    ·
      refine ⟨15536945942386738236214247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41431855846364635296571325 15536945942386738236214247)
      ·
        refine ⟨23305418913580107354321371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15536945942386738236214247 23305418913580107354321371)
        ·
          refine ⟨34958128370370161031482057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23305418913580107354321371 34958128370370161031482057)
          ·
            refine ⟨26218596277777620773611543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34958128370370161031482057 26218596277777620773611543)
            ·
              refine ⟨39327894416666431160417315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26218596277777620773611543 39327894416666431160417315)
              ·
                refine ⟨58991841624999646740625973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39327894416666431160417315 58991841624999646740625973)
                ·
                  refine ⟨5530485152343716881933685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 58991841624999646740625973 5530485152343716881933685)
                  ·
                    refine ⟨518482983032223457681283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5530485152343716881933685 518482983032223457681283)
                    ·
                      rfl

theorem cell23_3029226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 1, 5, 5].length) (baseStart_3029226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3029226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3029226 prefixEnd_3029226 := by exact prefixLift 3029226
  have htrace : WordTrace (prefixWord ++ tailWord_3029226) baseStart_3029226 baseEnd_3029226 := by
    simpa [prefixWord, tailWord_3029226, baseEnd_3029226] using wordTrace_append hprefix tailTrace_3029226
  have hstable : (prefixWord ++ tailWord_3029226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3029226).length < 2 ^ (prefixWord ++ tailWord_3029226).sum := by decide
  have hdescent : baseEnd_3029226 < baseStart_3029226 := by decide
  rcases family_descends (prefixWord ++ tailWord_3029226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3029233 : List Nat := [1, 2, 2, 2, 2, 1, 2, 2, 4, 3, 2]
def baseStart_3029233 : Nat := 118140960795 + 3029233 * 2 ^ 59
def prefixEnd_3029233 : Nat := 4983230072969 + 3 ^ 40 * 3029233 * 2
def baseEnd_3029233 : Nat := 1555452543461251845656317

theorem tailTrace_3029233 : CollatzResearch.WordTrace tailWord_3029233 prefixEnd_3029233 1555452543461251845656317 := by
  unfold tailWord_3029233
  simp only [CollatzResearch.WordTrace]
  refine ⟨110485204234613667653028353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73656802823075778435352235 110485204234613667653028353)
  ·
    refine ⟨82863903175960250739771265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110485204234613667653028353 82863903175960250739771265)
    ·
      refine ⟨62147927381970188054828449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82863903175960250739771265 62147927381970188054828449)
      ·
        refine ⟨46610945536477641041121337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62147927381970188054828449 46610945536477641041121337)
        ·
          refine ⟨34958209152358230780841003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46610945536477641041121337 34958209152358230780841003)
          ·
            refine ⟨52437313728537346171261505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34958209152358230780841003 52437313728537346171261505)
            ·
              refine ⟨39327985296403009628446129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52437313728537346171261505 39327985296403009628446129)
              ·
                refine ⟨29495988972302257221334597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39327985296403009628446129 29495988972302257221334597)
                ·
                  refine ⟨5530497932306673229000237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29495988972302257221334597 5530497932306673229000237)
                  ·
                    refine ⟨2073936724615002460875089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5530497932306673229000237 2073936724615002460875089)
                    ·
                      refine ⟨1555452543461251845656317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2073936724615002460875089 1555452543461251845656317)
                      ·
                        rfl

theorem cell23_3029233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 2, 4, 3, 2].length) (baseStart_3029233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3029233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3029233 prefixEnd_3029233 := by exact prefixLift 3029233
  have htrace : WordTrace (prefixWord ++ tailWord_3029233) baseStart_3029233 baseEnd_3029233 := by
    simpa [prefixWord, tailWord_3029233, baseEnd_3029233] using wordTrace_append hprefix tailTrace_3029233
  have hstable : (prefixWord ++ tailWord_3029233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3029233).length < 2 ^ (prefixWord ++ tailWord_3029233).sum := by decide
  have hdescent : baseEnd_3029233 < baseStart_3029233 := by decide
  rcases family_descends (prefixWord ++ tailWord_3029233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3029257 : List Nat := [1, 2, 1, 1, 3, 5, 2, 3, 1, 1, 3]
def baseStart_3029257 : Nat := 118140960795 + 3029257 * 2 ^ 59
def prefixEnd_3029257 : Nat := 4983230072969 + 3 ^ 40 * 3029257 * 2
def baseEnd_3029257 : Nat := 1555464866996959751756207

theorem tailTrace_3029257 : CollatzResearch.WordTrace tailWord_3029257 prefixEnd_3029257 1555464866996959751756207 := by
  unfold tailWord_3029257
  simp only [CollatzResearch.WordTrace]
  refine ⟨110486079586526719751902025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73657386391017813167934683 110486079586526719751902025)
  ·
    refine ⟨82864559689895039813926519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110486079586526719751902025 82864559689895039813926519)
    ·
      refine ⟨124296839534842559720889779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82864559689895039813926519 124296839534842559720889779)
      ·
        refine ⟨186445259302263839581334669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124296839534842559720889779 186445259302263839581334669)
        ·
          refine ⟨69916972238348939843000501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 186445259302263839581334669 69916972238348939843000501)
          ·
            refine ⟨6554716147345213110281297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 69916972238348939843000501 6554716147345213110281297)
            ·
              refine ⟨4916037110508909832710973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6554716147345213110281297 4916037110508909832710973)
              ·
                refine ⟨1843513916440841187266615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4916037110508909832710973 1843513916440841187266615)
                ·
                  refine ⟨2765270874661261780899923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1843513916440841187266615 2765270874661261780899923)
                  ·
                    refine ⟨4147906311991892671349885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2765270874661261780899923 4147906311991892671349885)
                    ·
                      refine ⟨1555464866996959751756207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4147906311991892671349885 1555464866996959751756207)
                      ·
                        rfl

theorem cell23_3029257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 2, 3, 1, 1, 3].length) (baseStart_3029257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3029257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3029257 prefixEnd_3029257 := by exact prefixLift 3029257
  have htrace : WordTrace (prefixWord ++ tailWord_3029257) baseStart_3029257 baseEnd_3029257 := by
    simpa [prefixWord, tailWord_3029257, baseEnd_3029257] using wordTrace_append hprefix tailTrace_3029257
  have hstable : (prefixWord ++ tailWord_3029257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3029257).length < 2 ^ (prefixWord ++ tailWord_3029257).sum := by decide
  have hdescent : baseEnd_3029257 < baseStart_3029257 := by decide
  rcases family_descends (prefixWord ++ tailWord_3029257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3029276 : List Nat := [2, 2, 3, 1, 1, 1, 1, 4, 1, 1, 6]
def baseStart_3029276 : Nat := 118140960795 + 3029276 * 2 ^ 59
def prefixEnd_3029276 : Nat := 4983230072969 + 3 ^ 40 * 3029276 * 2
def baseEnd_3029276 : Nat := 1555474623129395177418619

theorem tailTrace_3029276 : CollatzResearch.WordTrace tailWord_3029276 prefixEnd_3029276 1555474623129395177418619 := by
  unfold tailWord_3029276
  simp only [CollatzResearch.WordTrace]
  refine ⟨55243386286728942998421841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73657848382305257331229121 55243386286728942998421841)
  ·
    refine ⟨41432539715046707248816381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55243386286728942998421841 41432539715046707248816381)
    ·
      refine ⟨15537202393142515218306143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41432539715046707248816381 15537202393142515218306143)
      ·
        refine ⟨23305803589713772827459215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15537202393142515218306143 23305803589713772827459215)
        ·
          refine ⟨34958705384570659241188823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23305803589713772827459215 34958705384570659241188823)
          ·
            refine ⟨52438058076855988861783235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34958705384570659241188823 52438058076855988861783235)
            ·
              refine ⟨78657087115283983292674853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52438058076855988861783235 78657087115283983292674853)
              ·
                refine ⟨14748203834115746867376535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 78657087115283983292674853 14748203834115746867376535)
                ·
                  refine ⟨22122305751173620301064803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14748203834115746867376535 22122305751173620301064803)
                  ·
                    refine ⟨33183458626760430451597205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22122305751173620301064803 33183458626760430451597205)
                    ·
                      refine ⟨1555474623129395177418619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 33183458626760430451597205 1555474623129395177418619)
                      ·
                        rfl

theorem cell23_3029276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 4, 1, 1, 6].length) (baseStart_3029276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3029276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3029276 prefixEnd_3029276 := by exact prefixLift 3029276
  have htrace : WordTrace (prefixWord ++ tailWord_3029276) baseStart_3029276 baseEnd_3029276 := by
    simpa [prefixWord, tailWord_3029276, baseEnd_3029276] using wordTrace_append hprefix tailTrace_3029276
  have hstable : (prefixWord ++ tailWord_3029276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3029276).length < 2 ^ (prefixWord ++ tailWord_3029276).sum := by decide
  have hdescent : baseEnd_3029276 < baseStart_3029276 := by decide
  rcases family_descends (prefixWord ++ tailWord_3029276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3029330 : List Nat := [3, 2, 2, 1, 1, 1, 4, 1, 4, 1, 3]
def baseStart_3029330 : Nat := 118140960795 + 3029330 * 2 ^ 59
def prefixEnd_3029330 : Nat := 4983230072969 + 3 ^ 40 * 3029330 * 2
def baseEnd_3029330 : Nat := 1555502351084737966143371

theorem tailTrace_3029330 : CollatzResearch.WordTrace tailWord_3029330 prefixEnd_3029330 1555502351084737966143371 := by
  unfold tailWord_3029330
  simp only [CollatzResearch.WordTrace]
  refine ⟨27622185528815563304827361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73659161410174835479539629 27622185528815563304827361)
  ·
    refine ⟨20716639146611672478620521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27622185528815563304827361 20716639146611672478620521)
    ·
      refine ⟨15537479359958754358965391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20716639146611672478620521 15537479359958754358965391)
      ·
        refine ⟨23306219039938131538448087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15537479359958754358965391 23306219039938131538448087)
        ·
          refine ⟨34959328559907197307672131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23306219039938131538448087 34959328559907197307672131)
          ·
            refine ⟨52438992839860795961508197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34959328559907197307672131 52438992839860795961508197)
            ·
              refine ⟨9832311157473899242782787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 52438992839860795961508197 9832311157473899242782787)
              ·
                refine ⟨14748466736210848864174181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9832311157473899242782787 14748466736210848864174181)
                ·
                  refine ⟨2765337513039534162032659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14748466736210848864174181 2765337513039534162032659)
                  ·
                    refine ⟨4148006269559301243048989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2765337513039534162032659 4148006269559301243048989)
                    ·
                      refine ⟨1555502351084737966143371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4148006269559301243048989 1555502351084737966143371)
                      ·
                        rfl

theorem cell23_3029330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 4, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 4, 1, 4, 1, 3].length) (baseStart_3029330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3029330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3029330 prefixEnd_3029330 := by exact prefixLift 3029330
  have htrace : WordTrace (prefixWord ++ tailWord_3029330) baseStart_3029330 baseEnd_3029330 := by
    simpa [prefixWord, tailWord_3029330, baseEnd_3029330] using wordTrace_append hprefix tailTrace_3029330
  have hstable : (prefixWord ++ tailWord_3029330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3029330).length < 2 ^ (prefixWord ++ tailWord_3029330).sum := by decide
  have hdescent : baseEnd_3029330 < baseStart_3029330 := by decide
  rcases family_descends (prefixWord ++ tailWord_3029330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3029373 : List Nat := [1, 4, 1, 1, 2, 3, 2, 1, 2, 1, 5]
def baseStart_3029373 : Nat := 118140960795 + 3029373 * 2 ^ 59
def prefixEnd_3029373 : Nat := 4983230072969 + 3 ^ 40 * 3029373 * 2
def baseEnd_3029373 : Nat := 1555524430752881297905673

theorem tailTrace_3029373 : CollatzResearch.WordTrace tailWord_3029373 prefixEnd_3029373 1555524430752881297905673 := by
  unfold tailWord_3029373
  simp only [CollatzResearch.WordTrace]
  refine ⟨110490310454106471563124773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73660206969404314375416515 110490310454106471563124773)
  ·
    refine ⟨20716933210144963418085895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 110490310454106471563124773 20716933210144963418085895)
    ·
      refine ⟨31075399815217445127128843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20716933210144963418085895 31075399815217445127128843)
      ·
        refine ⟨46613099722826167690693265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31075399815217445127128843 46613099722826167690693265)
        ·
          refine ⟨34959824792119625768019949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46613099722826167690693265 34959824792119625768019949)
          ·
            refine ⟨13109934297044859663007481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34959824792119625768019949 13109934297044859663007481)
            ·
              refine ⟨9832450722783644747255611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13109934297044859663007481 9832450722783644747255611)
              ·
                refine ⟨14748676084175467120883417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9832450722783644747255611 14748676084175467120883417)
                ·
                  refine ⟨11061507063131600340662563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14748676084175467120883417 11061507063131600340662563)
                  ·
                    refine ⟨16592260594697400510993845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11061507063131600340662563 16592260594697400510993845)
                    ·
                      refine ⟨1555524430752881297905673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16592260594697400510993845 1555524430752881297905673)
                      ·
                        rfl

theorem cell23_3029373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 2, 1, 2, 1, 5].length) (baseStart_3029373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3029373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3029373 prefixEnd_3029373 := by exact prefixLift 3029373
  have htrace : WordTrace (prefixWord ++ tailWord_3029373) baseStart_3029373 baseEnd_3029373 := by
    simpa [prefixWord, tailWord_3029373, baseEnd_3029373] using wordTrace_append hprefix tailTrace_3029373
  have hstable : (prefixWord ++ tailWord_3029373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3029373).length < 2 ^ (prefixWord ++ tailWord_3029373).sum := by decide
  have hdescent : baseEnd_3029373 < baseStart_3029373 := by decide
  rcases family_descends (prefixWord ++ tailWord_3029373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3029383 : List Nat := [1, 1, 4, 2, 2, 1, 2, 2, 2, 2, 4]
def baseStart_3029383 : Nat := 118140960795 + 3029383 * 2 ^ 59
def prefixEnd_3029383 : Nat := 4983230072969 + 3 ^ 40 * 3029383 * 2
def baseEnd_3029383 : Nat := 1555529565559426258780627

theorem tailTrace_3029383 : CollatzResearch.WordTrace tailWord_3029383 prefixEnd_3029383 1555529565559426258780627 := by
  unfold tailWord_3029383
  simp only [CollatzResearch.WordTrace]
  refine ⟨110490675184070243270988803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73660450122713495513992535 110490675184070243270988803)
  ·
    refine ⟨165736012776105364906483205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110490675184070243270988803 165736012776105364906483205)
    ·
      refine ⟨31075502395519755919965601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 165736012776105364906483205 31075502395519755919965601)
      ·
        refine ⟨23306626796639816939974201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31075502395519755919965601 23306626796639816939974201)
        ·
          refine ⟨17479970097479862704980651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23306626796639816939974201 17479970097479862704980651)
          ·
            refine ⟨26219955146219794057470977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17479970097479862704980651 26219955146219794057470977)
            ·
              refine ⟨19664966359664845543103233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26219955146219794057470977 19664966359664845543103233)
              ·
                refine ⟨14748724769748634157327425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19664966359664845543103233 14748724769748634157327425)
                ·
                  refine ⟨11061543577311475617995569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14748724769748634157327425 11061543577311475617995569)
                  ·
                    refine ⟨8296157682983606713496677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11061543577311475617995569 8296157682983606713496677)
                    ·
                      refine ⟨1555529565559426258780627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8296157682983606713496677 1555529565559426258780627)
                      ·
                        rfl

theorem cell23_3029383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 2, 2, 2, 2, 4].length) (baseStart_3029383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3029383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3029383 prefixEnd_3029383 := by exact prefixLift 3029383
  have htrace : WordTrace (prefixWord ++ tailWord_3029383) baseStart_3029383 baseEnd_3029383 := by
    simpa [prefixWord, tailWord_3029383, baseEnd_3029383] using wordTrace_append hprefix tailTrace_3029383
  have hstable : (prefixWord ++ tailWord_3029383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3029383).length < 2 ^ (prefixWord ++ tailWord_3029383).sum := by decide
  have hdescent : baseEnd_3029383 < baseStart_3029383 := by decide
  rcases family_descends (prefixWord ++ tailWord_3029383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3029387 : List Nat := [1, 1, 1, 1, 4, 4, 1, 4, 2, 2, 2]
def baseStart_3029387 : Nat := 118140960795 + 3029387 * 2 ^ 59
def prefixEnd_3029387 : Nat := 4983230072969 + 3 ^ 40 * 3029387 * 2
def baseEnd_3029387 : Nat := 1555531619482044243130609

theorem tailTrace_3029387 : CollatzResearch.WordTrace tailWord_3029387 prefixEnd_3029387 1555531619482044243130609 := by
  unfold tailWord_3029387
  simp only [CollatzResearch.WordTrace]
  refine ⟨110490821076055751954134415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73660547384037167969422943 110490821076055751954134415)
  ·
    refine ⟨165736231614083627931201623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110490821076055751954134415 165736231614083627931201623)
    ·
      refine ⟨248604347421125441896802435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165736231614083627931201623 248604347421125441896802435)
      ·
        refine ⟨372906521131688162845203653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 248604347421125441896802435 372906521131688162845203653)
        ·
          refine ⟨69919972712191530533475685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 372906521131688162845203653 69919972712191530533475685)
          ·
            refine ⟨13109994883535911975026691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 69919972712191530533475685 13109994883535911975026691)
            ·
              refine ⟨19664992325303867962540037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13109994883535911975026691 19664992325303867962540037)
              ·
                refine ⟨3687186060994475242976257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19664992325303867962540037 3687186060994475242976257)
                ·
                  refine ⟨2765389545745856432232193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3687186060994475242976257 2765389545745856432232193)
                  ·
                    refine ⟨2074042159309392324174145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2765389545745856432232193 2074042159309392324174145)
                    ·
                      refine ⟨1555531619482044243130609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2074042159309392324174145 1555531619482044243130609)
                      ·
                        rfl

theorem cell23_3029387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 1, 4, 2, 2, 2].length) (baseStart_3029387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3029387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3029387 prefixEnd_3029387 := by exact prefixLift 3029387
  have htrace : WordTrace (prefixWord ++ tailWord_3029387) baseStart_3029387 baseEnd_3029387 := by
    simpa [prefixWord, tailWord_3029387, baseEnd_3029387] using wordTrace_append hprefix tailTrace_3029387
  have hstable : (prefixWord ++ tailWord_3029387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3029387).length < 2 ^ (prefixWord ++ tailWord_3029387).sum := by decide
  have hdescent : baseEnd_3029387 < baseStart_3029387 := by decide
  rcases family_descends (prefixWord ++ tailWord_3029387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3029390 : List Nat := [4, 1, 1, 4, 1, 1, 1, 1, 2, 4, 3]
def baseStart_3029390 : Nat := 118140960795 + 3029390 * 2 ^ 59
def prefixEnd_3029390 : Nat := 4983230072969 + 3 ^ 40 * 3029390 * 2
def baseEnd_3029390 : Nat := 1555533159924007731393095

theorem tailTrace_3029390 : CollatzResearch.WordTrace tailWord_3029390 prefixEnd_3029390 1555533159924007731393095 := by
  unfold tailWord_3029390
  simp only [CollatzResearch.WordTrace]
  refine ⟨13811366311880610433311703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 73660620330029922310995749 13811366311880610433311703)
  ·
    refine ⟨20717049467820915649967555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13811366311880610433311703 20717049467820915649967555)
    ·
      refine ⟨31075574201731373474951333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20717049467820915649967555 31075574201731373474951333)
      ·
        refine ⟨5826670162824632526553375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31075574201731373474951333 5826670162824632526553375)
        ·
          refine ⟨8740005244236948789830063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5826670162824632526553375 8740005244236948789830063)
          ·
            refine ⟨13110007866355423184745095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8740005244236948789830063 13110007866355423184745095)
            ·
              refine ⟨19665011799533134777117643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13110007866355423184745095 19665011799533134777117643)
              ·
                refine ⟨29497517699299702165676465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19665011799533134777117643 29497517699299702165676465)
                ·
                  refine ⟨22123138274474776624257349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29497517699299702165676465 22123138274474776624257349)
                  ·
                    refine ⟨4148088426464020617048253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22123138274474776624257349 4148088426464020617048253)
                    ·
                      refine ⟨1555533159924007731393095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4148088426464020617048253 1555533159924007731393095)
                      ·
                        rfl

theorem cell23_3029390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 1, 1, 2, 4, 3].length) (baseStart_3029390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3029390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3029390 prefixEnd_3029390 := by exact prefixLift 3029390
  have htrace : WordTrace (prefixWord ++ tailWord_3029390) baseStart_3029390 baseEnd_3029390 := by
    simpa [prefixWord, tailWord_3029390, baseEnd_3029390] using wordTrace_append hprefix tailTrace_3029390
  have hstable : (prefixWord ++ tailWord_3029390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3029390).length < 2 ^ (prefixWord ++ tailWord_3029390).sum := by decide
  have hdescent : baseEnd_3029390 < baseStart_3029390 := by decide
  rcases family_descends (prefixWord ++ tailWord_3029390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3029400 : List Nat := [2, 1, 2, 5, 1, 2, 1, 1, 2, 2, 4]
def baseStart_3029400 : Nat := 118140960795 + 3029400 * 2 ^ 59
def prefixEnd_3029400 : Nat := 4983230072969 + 3 ^ 40 * 3029400 * 2
def baseEnd_3029400 : Nat := 1555538294730552692268049

theorem tailTrace_3029400 : CollatzResearch.WordTrace tailWord_3029400 prefixEnd_3029400 1555538294730552692268049 := by
  unfold tailWord_3029400
  simp only [CollatzResearch.WordTrace]
  refine ⟨55245647612504327587178827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73660863483339103449571769 55245647612504327587178827)
  ·
    refine ⟨82868471418756491380768241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55245647612504327587178827 82868471418756491380768241)
    ·
      refine ⟨62151353564067368535576181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82868471418756491380768241 62151353564067368535576181)
      ·
        refine ⟨5826689396631315800210267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 62151353564067368535576181 5826689396631315800210267)
        ·
          refine ⟨8740034094946973700315401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5826689396631315800210267 8740034094946973700315401)
          ·
            refine ⟨6555025571210230275236551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8740034094946973700315401 6555025571210230275236551)
            ·
              refine ⟨9832538356815345412854827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6555025571210230275236551 9832538356815345412854827)
              ·
                refine ⟨14748807535223018119282241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9832538356815345412854827 14748807535223018119282241)
                ·
                  refine ⟨11061605651417263589461681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14748807535223018119282241 11061605651417263589461681)
                  ·
                    refine ⟨8296204238562947692096261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11061605651417263589461681 8296204238562947692096261)
                    ·
                      refine ⟨1555538294730552692268049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8296204238562947692096261 1555538294730552692268049)
                      ·
                        rfl

theorem cell23_3029400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 1, 1, 2, 2, 4].length) (baseStart_3029400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3029400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3029400 prefixEnd_3029400 := by exact prefixLift 3029400
  have htrace : WordTrace (prefixWord ++ tailWord_3029400) baseStart_3029400 baseEnd_3029400 := by
    simpa [prefixWord, tailWord_3029400, baseEnd_3029400] using wordTrace_append hprefix tailTrace_3029400
  have hstable : (prefixWord ++ tailWord_3029400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3029400).length < 2 ^ (prefixWord ++ tailWord_3029400).sum := by decide
  have hdescent : baseEnd_3029400 < baseStart_3029400 := by decide
  rcases family_descends (prefixWord ++ tailWord_3029400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3029443 : List Nat := [1, 1, 1, 3, 1, 1, 3, 3, 4, 1, 4]
def baseStart_3029443 : Nat := 118140960795 + 3029443 * 2 ^ 59
def prefixEnd_3029443 : Nat := 4983230072969 + 3 ^ 40 * 3029443 * 2
def baseEnd_3029443 : Nat := 1555560374398696024030351

theorem tailTrace_3029443 : CollatzResearch.WordTrace tailWord_3029443 prefixEnd_3029443 1555560374398696024030351 := by
  unfold tailWord_3029443
  simp only [CollatzResearch.WordTrace]
  refine ⟨110492863563852873518172983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73661909042568582345448655 110492863563852873518172983)
  ·
    refine ⟨165739295345779310277259475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110492863563852873518172983 165739295345779310277259475)
    ·
      refine ⟨248608943018668965415889213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165739295345779310277259475 248608943018668965415889213)
      ·
        refine ⟨93228353632000862030958455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 248608943018668965415889213 93228353632000862030958455)
        ·
          refine ⟨139842530448001293046437683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93228353632000862030958455 139842530448001293046437683)
          ·
            refine ⟨209763795672001939569656525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 139842530448001293046437683 209763795672001939569656525)
            ·
              refine ⟨78661423377000727338621197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 209763795672001939569656525 78661423377000727338621197)
              ·
                refine ⟨29498033766375272751982949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 78661423377000727338621197 29498033766375272751982949)
                ·
                  refine ⟨5530881331195363640996803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29498033766375272751982949 5530881331195363640996803)
                  ·
                    refine ⟨8296321996793045461495205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5530881331195363640996803 8296321996793045461495205)
                    ·
                      refine ⟨1555560374398696024030351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8296321996793045461495205 1555560374398696024030351)
                      ·
                        rfl

theorem cell23_3029443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 3, 4, 1, 4].length) (baseStart_3029443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3029443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3029443 prefixEnd_3029443 := by exact prefixLift 3029443
  have htrace : WordTrace (prefixWord ++ tailWord_3029443) baseStart_3029443 baseEnd_3029443 := by
    simpa [prefixWord, tailWord_3029443, baseEnd_3029443] using wordTrace_append hprefix tailTrace_3029443
  have hstable : (prefixWord ++ tailWord_3029443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3029443).length < 2 ^ (prefixWord ++ tailWord_3029443).sum := by decide
  have hdescent : baseEnd_3029443 < baseStart_3029443 := by decide
  rcases family_descends (prefixWord ++ tailWord_3029443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3029460 : List Nat := [2, 4, 1, 2, 2, 1, 1, 2, 1, 3, 4]
def baseStart_3029460 : Nat := 118140960795 + 3029460 * 2 ^ 59
def prefixEnd_3029460 : Nat := 4983230072969 + 3 ^ 40 * 3029460 * 2
def baseEnd_3029460 : Nat := 1555569103569822457517773

theorem tailTrace_3029460 : CollatzResearch.WordTrace tailWord_3029460 prefixEnd_3029460 1555569103569822457517773 := by
  unfold tailWord_3029460
  simp only [CollatzResearch.WordTrace]
  refine ⟨55246741802395642710770917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73662322403194190281027889 55246741802395642710770917)
  ·
    refine ⟨10358764087949183008269547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 55246741802395642710770917 10358764087949183008269547)
    ·
      refine ⟨15538146131923774512404321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10358764087949183008269547 15538146131923774512404321)
      ·
        refine ⟨11653609598942830884303241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15538146131923774512404321 11653609598942830884303241)
        ·
          refine ⟨8740207199207123163227431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11653609598942830884303241 8740207199207123163227431)
          ·
            refine ⟨13110310798810684744841147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8740207199207123163227431 13110310798810684744841147)
            ·
              refine ⟨19665466198216027117261721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13110310798810684744841147 19665466198216027117261721)
              ·
                refine ⟨14749099648662020337946291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19665466198216027117261721 14749099648662020337946291)
                ·
                  refine ⟨22123649472993030506919437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14749099648662020337946291 22123649472993030506919437)
                  ·
                    refine ⟨8296368552372386440094789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22123649472993030506919437 8296368552372386440094789)
                    ·
                      refine ⟨1555569103569822457517773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8296368552372386440094789 1555569103569822457517773)
                      ·
                        rfl

theorem cell23_3029460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 1, 2, 1, 3, 4].length) (baseStart_3029460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3029460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3029460 prefixEnd_3029460 := by exact prefixLift 3029460
  have htrace : WordTrace (prefixWord ++ tailWord_3029460) baseStart_3029460 baseEnd_3029460 := by
    simpa [prefixWord, tailWord_3029460, baseEnd_3029460] using wordTrace_append hprefix tailTrace_3029460
  have hstable : (prefixWord ++ tailWord_3029460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3029460).length < 2 ^ (prefixWord ++ tailWord_3029460).sum := by decide
  have hdescent : baseEnd_3029460 < baseStart_3029460 := by decide
  rcases family_descends (prefixWord ++ tailWord_3029460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3029473 : List Nat := [1, 2, 3, 1, 2, 2, 1, 1, 2, 4, 4]
def baseStart_3029473 : Nat := 118140960795 + 3029473 * 2 ^ 59
def prefixEnd_3029473 : Nat := 4983230072969 + 3 ^ 40 * 3029473 * 2
def baseEnd_3029473 : Nat := 1555575778818330906655213

theorem tailTrace_3029473 : CollatzResearch.WordTrace tailWord_3029473 prefixEnd_3029473 1555575778818330906655213 := by
  unfold tailWord_3029473
  simp only [CollatzResearch.WordTrace]
  refine ⟨110493957753744188641765073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73662638502496125761176715 110493957753744188641765073)
  ·
    refine ⟨82870468315308141481323805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110493957753744188641765073 82870468315308141481323805)
    ·
      refine ⟨31076425618240553055496427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82870468315308141481323805 31076425618240553055496427)
      ·
        refine ⟨46614638427360829583244641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31076425618240553055496427 46614638427360829583244641)
        ·
          refine ⟨34960978820520622187433481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46614638427360829583244641 34960978820520622187433481)
          ·
            refine ⟨26220734115390466640575111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34960978820520622187433481 26220734115390466640575111)
            ·
              refine ⟨39331101173085699960862667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26220734115390466640575111 39331101173085699960862667)
              ·
                refine ⟨58996651759628549941294001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39331101173085699960862667 58996651759628549941294001)
                ·
                  refine ⟨44247488819721412455970501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 58996651759628549941294001 44247488819721412455970501)
                  ·
                    refine ⟨8296404153697764835494469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 44247488819721412455970501 8296404153697764835494469)
                    ·
                      refine ⟨1555575778818330906655213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8296404153697764835494469 1555575778818330906655213)
                      ·
                        rfl

theorem cell23_3029473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 1, 2, 4, 4].length) (baseStart_3029473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3029473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3029473 prefixEnd_3029473 := by exact prefixLift 3029473
  have htrace : WordTrace (prefixWord ++ tailWord_3029473) baseStart_3029473 baseEnd_3029473 := by
    simpa [prefixWord, tailWord_3029473, baseEnd_3029473] using wordTrace_append hprefix tailTrace_3029473
  have hstable : (prefixWord ++ tailWord_3029473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3029473).length < 2 ^ (prefixWord ++ tailWord_3029473).sum := by decide
  have hdescent : baseEnd_3029473 < baseStart_3029473 := by decide
  rcases family_descends (prefixWord ++ tailWord_3029473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3029480 : List Nat := [2, 1, 4, 1, 1, 3, 2, 1, 1, 4, 3]
def baseStart_3029480 : Nat := 118140960795 + 3029480 * 2 ^ 59
def prefixEnd_3029480 : Nat := 4983230072969 + 3 ^ 40 * 3029480 * 2
def baseEnd_3029480 : Nat := 1555579373182912379267681

theorem tailTrace_3029480 : CollatzResearch.WordTrace tailWord_3029480 prefixEnd_3029480 1555579373182912379267681 := by
  unfold tailWord_3029480
  simp only [CollatzResearch.WordTrace]
  refine ⟨55247106532359414418634947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73662808709812552558179929 55247106532359414418634947)
  ·
    refine ⟨82870659798539121627952421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55247106532359414418634947 82870659798539121627952421)
    ·
      refine ⟨15538248712226085305241079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 82870659798539121627952421 15538248712226085305241079)
      ·
        refine ⟨23307373068339127957861619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15538248712226085305241079 23307373068339127957861619)
        ·
          refine ⟨34961059602508691936792429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23307373068339127957861619 34961059602508691936792429)
          ·
            refine ⟨13110397350940759476297161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34961059602508691936792429 13110397350940759476297161)
            ·
              refine ⟨9832798013205569607222871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13110397350940759476297161 9832798013205569607222871)
              ·
                refine ⟨14749197019808354410834307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9832798013205569607222871 14749197019808354410834307)
                ·
                  refine ⟨22123795529712531616251461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14749197019808354410834307 22123795529712531616251461)
                  ·
                    refine ⟨4148211661821099678047149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22123795529712531616251461 4148211661821099678047149)
                    ·
                      refine ⟨1555579373182912379267681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4148211661821099678047149 1555579373182912379267681)
                      ·
                        rfl

theorem cell23_3029480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 2, 1, 1, 4, 3].length) (baseStart_3029480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3029480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3029480 prefixEnd_3029480 := by exact prefixLift 3029480
  have htrace : WordTrace (prefixWord ++ tailWord_3029480) baseStart_3029480 baseEnd_3029480 := by
    simpa [prefixWord, tailWord_3029480, baseEnd_3029480] using wordTrace_append hprefix tailTrace_3029480
  have hstable : (prefixWord ++ tailWord_3029480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3029480).length < 2 ^ (prefixWord ++ tailWord_3029480).sum := by decide
  have hdescent : baseEnd_3029480 < baseStart_3029480 := by decide
  rcases family_descends (prefixWord ++ tailWord_3029480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3029598 : List Nat := [4, 4, 1, 2, 1, 1, 1, 3, 1, 5]
def baseStart_3029598 : Nat := 118140960795 + 3029598 * 2 ^ 59
def prefixEnd_3029598 : Nat := 4983230072969 + 3 ^ 40 * 3029598 * 2
def baseEnd_3029598 : Nat := 518546654633380972530713

theorem tailTrace_3029598 : CollatzResearch.WordTrace tailWord_3029598 prefixEnd_3029598 518546654633380972530713 := by
  unfold tailWord_3029598
  simp only [CollatzResearch.WordTrace]
  refine ⟨13812314609786416873758181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 73665677918860889993376965 13812314609786416873758181)
  ·
    refine ⟨2589808989334953163829659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13812314609786416873758181 2589808989334953163829659)
    ·
      refine ⟨3884713484002429745744489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2589808989334953163829659 3884713484002429745744489)
      ·
        refine ⟨2913535113001822309308367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3884713484002429745744489 2913535113001822309308367)
        ·
          refine ⟨4370302669502733463962551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2913535113001822309308367 4370302669502733463962551)
          ·
            refine ⟨6555454004254100195943827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4370302669502733463962551 6555454004254100195943827)
            ·
              refine ⟨9833181006381150293915741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6555454004254100195943827 9833181006381150293915741)
              ·
                refine ⟨3687442877392931360218403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9833181006381150293915741 3687442877392931360218403)
                ·
                  refine ⟨5531164316089397040327605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3687442877392931360218403 5531164316089397040327605)
                  ·
                    refine ⟨518546654633380972530713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5531164316089397040327605 518546654633380972530713)
                    ·
                      rfl

theorem cell23_3029598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 1, 3, 1, 5].length) (baseStart_3029598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3029598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3029598 prefixEnd_3029598 := by exact prefixLift 3029598
  have htrace : WordTrace (prefixWord ++ tailWord_3029598) baseStart_3029598 baseEnd_3029598 := by
    simpa [prefixWord, tailWord_3029598, baseEnd_3029598] using wordTrace_append hprefix tailTrace_3029598
  have hstable : (prefixWord ++ tailWord_3029598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3029598).length < 2 ^ (prefixWord ++ tailWord_3029598).sum := by decide
  have hdescent : baseEnd_3029598 < baseStart_3029598 := by decide
  rcases family_descends (prefixWord ++ tailWord_3029598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3029601 : List Nat := [1, 2, 3, 1, 1, 4, 1, 5, 1, 2, 2]
def baseStart_3029601 : Nat := 118140960795 + 3029601 * 2 ^ 59
def prefixEnd_3029601 : Nat := 4983230072969 + 3 ^ 40 * 3029601 * 2
def baseEnd_3029601 : Nat := 1555641504342106405854625

theorem tailTrace_3029601 : CollatzResearch.WordTrace tailWord_3029601 prefixEnd_3029601 1555641504342106405854625 := by
  unfold tailWord_3029601
  simp only [CollatzResearch.WordTrace]
  refine ⟨110498626297280466502424657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73665750864853644334949771 110498626297280466502424657)
  ·
    refine ⟨82873969722960349876818493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110498626297280466502424657 82873969722960349876818493)
    ·
      refine ⟨31077738646110131203806935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82873969722960349876818493 31077738646110131203806935)
      ·
        refine ⟨46616607969165196805710403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31077738646110131203806935 46616607969165196805710403)
        ·
          refine ⟨69924911953747795208565605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46616607969165196805710403 69924911953747795208565605)
          ·
            refine ⟨13110920991327711601606051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 69924911953747795208565605 13110920991327711601606051)
            ·
              refine ⟨19666381486991567402409077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13110920991327711601606051 19666381486991567402409077)
              ·
                refine ⟨1843723264405459443975851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 19666381486991567402409077 1843723264405459443975851)
                ·
                  refine ⟨2765584896608189165963777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1843723264405459443975851 2765584896608189165963777)
                  ·
                    refine ⟨2074188672456141874472833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2765584896608189165963777 2074188672456141874472833)
                    ·
                      refine ⟨1555641504342106405854625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2074188672456141874472833 1555641504342106405854625)
                      ·
                        rfl

theorem cell23_3029601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 1, 5, 1, 2, 2].length) (baseStart_3029601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3029601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3029601 prefixEnd_3029601 := by exact prefixLift 3029601
  have htrace : WordTrace (prefixWord ++ tailWord_3029601) baseStart_3029601 baseEnd_3029601 := by
    simpa [prefixWord, tailWord_3029601, baseEnd_3029601] using wordTrace_append hprefix tailTrace_3029601
  have hstable : (prefixWord ++ tailWord_3029601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3029601).length < 2 ^ (prefixWord ++ tailWord_3029601).sum := by decide
  have hdescent : baseEnd_3029601 < baseStart_3029601 := by decide
  rcases family_descends (prefixWord ++ tailWord_3029601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3029627 : List Nat := [1, 1, 1, 1, 1, 4, 2, 4, 3, 3, 2]
def baseStart_3029627 : Nat := 118140960795 + 3029627 * 2 ^ 59
def prefixEnd_3029627 : Nat := 4983230072969 + 3 ^ 40 * 3029627 * 2
def baseEnd_3029627 : Nat := 1555654854839123304129505

theorem tailTrace_3029627 : CollatzResearch.WordTrace tailWord_3029627 prefixEnd_3029627 1555654854839123304129505 := by
  unfold tailWord_3029627
  simp only [CollatzResearch.WordTrace]
  refine ⟨110499574595186272942871135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73666383063457515295247423 110499574595186272942871135)
  ·
    refine ⟨165749361892779409414306703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110499574595186272942871135 165749361892779409414306703)
    ·
      refine ⟨248624042839169114121460055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165749361892779409414306703 248624042839169114121460055)
      ·
        refine ⟨372936064258753671182190083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 248624042839169114121460055 372936064258753671182190083)
        ·
          refine ⟨559404096388130506773285125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 372936064258753671182190083 559404096388130506773285125)
          ·
            refine ⟨104888268072774470019990961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 559404096388130506773285125 104888268072774470019990961)
            ·
              refine ⟨78666201054580852514993221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 104888268072774470019990961 78666201054580852514993221)
              ·
                refine ⟨14749912697733909846561229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 78666201054580852514993221 14749912697733909846561229)
                ·
                  refine ⟨5531217261650216192460461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14749912697733909846561229 5531217261650216192460461)
                  ·
                    refine ⟨2074206473118831072172673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5531217261650216192460461 2074206473118831072172673)
                    ·
                      refine ⟨1555654854839123304129505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2074206473118831072172673 1555654854839123304129505)
                      ·
                        rfl

theorem cell23_3029627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 4, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 4, 3, 3, 2].length) (baseStart_3029627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3029627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3029627 prefixEnd_3029627 := by exact prefixLift 3029627
  have htrace : WordTrace (prefixWord ++ tailWord_3029627) baseStart_3029627 baseEnd_3029627 := by
    simpa [prefixWord, tailWord_3029627, baseEnd_3029627] using wordTrace_append hprefix tailTrace_3029627
  have hstable : (prefixWord ++ tailWord_3029627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3029627).length < 2 ^ (prefixWord ++ tailWord_3029627).sum := by decide
  have hdescent : baseEnd_3029627 < baseStart_3029627 := by decide
  rcases family_descends (prefixWord ++ tailWord_3029627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3029657 : List Nat := [1, 2, 1, 2, 1, 2, 4, 1, 3, 4, 2]
def baseStart_3029657 : Nat := 118140960795 + 3029657 * 2 ^ 59
def prefixEnd_3029657 : Nat := 4983230072969 + 3 ^ 40 * 3029657 * 2
def baseEnd_3029657 : Nat := 1555670259258758186754367

theorem tailTrace_3029657 : CollatzResearch.WordTrace tailWord_3029657 prefixEnd_3029657 1555670259258758186754367 := by
  unfold tailWord_3029657
  simp only [CollatzResearch.WordTrace]
  refine ⟨110500668785077588066463225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73667112523385058710975483 110500668785077588066463225)
  ·
    refine ⟨82875501588808191049847419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110500668785077588066463225 82875501588808191049847419)
    ·
      refine ⟨124313252383212286574771129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82875501588808191049847419 124313252383212286574771129)
      ·
        refine ⟨93234939287409214931078347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 124313252383212286574771129 93234939287409214931078347)
        ·
          refine ⟨139852408931113822396617521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93234939287409214931078347 139852408931113822396617521)
          ·
            refine ⟨104889306698335366797463141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 139852408931113822396617521 104889306698335366797463141)
            ·
              refine ⟨19666745005937881274524339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 104889306698335366797463141 19666745005937881274524339)
              ·
                refine ⟨29500117508906821911786509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19666745005937881274524339 29500117508906821911786509)
                ·
                  refine ⟨11062544065840058216919941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29500117508906821911786509 11062544065840058216919941)
                  ·
                    refine ⟨2074227012345010915672489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11062544065840058216919941 2074227012345010915672489)
                    ·
                      refine ⟨1555670259258758186754367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2074227012345010915672489 1555670259258758186754367)
                      ·
                        rfl

theorem cell23_3029657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 4, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 4, 1, 3, 4, 2].length) (baseStart_3029657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3029657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3029657 prefixEnd_3029657 := by exact prefixLift 3029657
  have htrace : WordTrace (prefixWord ++ tailWord_3029657) baseStart_3029657 baseEnd_3029657 := by
    simpa [prefixWord, tailWord_3029657, baseEnd_3029657] using wordTrace_append hprefix tailTrace_3029657
  have hstable : (prefixWord ++ tailWord_3029657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3029657).length < 2 ^ (prefixWord ++ tailWord_3029657).sum := by decide
  have hdescent : baseEnd_3029657 < baseStart_3029657 := by decide
  rcases family_descends (prefixWord ++ tailWord_3029657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3029727 : List Nat := [1, 1, 2, 3, 2, 3, 2, 2, 2, 5]
def baseStart_3029727 : Nat := 118140960795 + 3029727 * 2 ^ 59
def prefixEnd_3029727 : Nat := 4983230072969 + 3 ^ 40 * 3029727 * 2
def baseEnd_3029727 : Nat := 518568734301524304293015

theorem tailTrace_3029727 : CollatzResearch.WordTrace tailWord_3029727 prefixEnd_3029727 518568734301524304293015 := by
  unfold tailWord_3029727
  simp only [CollatzResearch.WordTrace]
  refine ⟨110503221894823990021511435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73668814596549326681007623 110503221894823990021511435)
  ·
    refine ⟨165754832842235985032267153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110503221894823990021511435 165754832842235985032267153)
    ·
      refine ⟨124316124631676988774200365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 165754832842235985032267153 124316124631676988774200365)
      ·
        refine ⟨46618546736878870790325137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 124316124631676988774200365 46618546736878870790325137)
        ·
          refine ⟨34963910052659153092743853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46618546736878870790325137 34963910052659153092743853)
          ·
            refine ⟨13111466269747182409778945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34963910052659153092743853 13111466269747182409778945)
            ·
              refine ⟨9833599702310386807334209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13111466269747182409778945 9833599702310386807334209)
              ·
                refine ⟨7375199776732790105500657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9833599702310386807334209 7375199776732790105500657)
                ·
                  refine ⟨5531399832549592579125493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7375199776732790105500657 5531399832549592579125493)
                  ·
                    refine ⟨518568734301524304293015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5531399832549592579125493 518568734301524304293015)
                    ·
                      rfl

theorem cell23_3029727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 2, 2, 2, 5].length) (baseStart_3029727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3029727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3029727 prefixEnd_3029727 := by exact prefixLift 3029727
  have htrace : WordTrace (prefixWord ++ tailWord_3029727) baseStart_3029727 baseEnd_3029727 := by
    simpa [prefixWord, tailWord_3029727, baseEnd_3029727] using wordTrace_append hprefix tailTrace_3029727
  have hstable : (prefixWord ++ tailWord_3029727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3029727).length < 2 ^ (prefixWord ++ tailWord_3029727).sum := by decide
  have hdescent : baseEnd_3029727 < baseStart_3029727 := by decide
  rcases family_descends (prefixWord ++ tailWord_3029727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3029731 : List Nat := [1, 1, 1, 7, 1, 1, 4, 2, 5]
def baseStart_3029731 : Nat := 118140960795 + 3029731 * 2 ^ 59
def prefixEnd_3029731 : Nat := 4983230072969 + 3 ^ 40 * 3029731 * 2
def baseEnd_3029731 : Nat := 172856472980798988581003

theorem tailTrace_3029731 : CollatzResearch.WordTrace tailWord_3029731 prefixEnd_3029731 172856472980798988581003 := by
  unfold tailWord_3029731
  simp only [CollatzResearch.WordTrace]
  refine ⟨110503367786809498704657047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73668911857872999136438031 110503367786809498704657047)
  ·
    refine ⟨165755051680214248056985571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110503367786809498704657047 165755051680214248056985571)
    ·
      refine ⟨248632577520321372085478357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165755051680214248056985571 248632577520321372085478357)
      ·
        refine ⟨5827326035632532158253399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 248632577520321372085478357 5827326035632532158253399)
        ·
          refine ⟨8740989053448798237380099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5827326035632532158253399 8740989053448798237380099)
          ·
            refine ⟨13111483580173197356070149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8740989053448798237380099 13111483580173197356070149)
            ·
              refine ⟨2458403171282474504263153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13111483580173197356070149 2458403171282474504263153)
              ·
                refine ⟨1843802378461855878197365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2458403171282474504263153 1843802378461855878197365)
                ·
                  refine ⟨172856472980798988581003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1843802378461855878197365 172856472980798988581003)
                  ·
                    rfl

theorem cell23_3029731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 4, 2, 5].length) (baseStart_3029731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3029731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3029731 prefixEnd_3029731 := by exact prefixLift 3029731
  have htrace : WordTrace (prefixWord ++ tailWord_3029731) baseStart_3029731 baseEnd_3029731 := by
    simpa [prefixWord, tailWord_3029731, baseEnd_3029731] using wordTrace_append hprefix tailTrace_3029731
  have hstable : (prefixWord ++ tailWord_3029731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3029731).length < 2 ^ (prefixWord ++ tailWord_3029731).sum := by decide
  have hdescent : baseEnd_3029731 < baseStart_3029731 := by decide
  rcases family_descends (prefixWord ++ tailWord_3029731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3029740 : List Nat := [2, 2, 1, 1, 2, 2, 1, 2, 2, 8]
def baseStart_3029740 : Nat := 118140960795 + 3029740 * 2 ^ 59
def prefixEnd_3029740 : Nat := 4983230072969 + 3 ^ 40 * 3029740 * 2
def baseEnd_3029740 : Nat := 518570959384360454005495

theorem tailTrace_3029740 : CollatzResearch.WordTrace tailWord_3029740 prefixEnd_3029740 518570959384360454005495 := by
  unfold tailWord_3029740
  simp only [CollatzResearch.WordTrace]
  refine ⟨55251848021888446620867337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73669130695851262161156449 55251848021888446620867337)
  ·
    refine ⟨41438886016416334965650503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55251848021888446620867337 41438886016416334965650503)
    ·
      refine ⟨62158329024624502448475755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41438886016416334965650503 62158329024624502448475755)
      ·
        refine ⟨93237493536936753672713633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62158329024624502448475755 93237493536936753672713633)
        ·
          refine ⟨69928120152702565254535225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93237493536936753672713633 69928120152702565254535225)
          ·
            refine ⟨52446090114526923940901419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69928120152702565254535225 52446090114526923940901419)
            ·
              refine ⟨78669135171790385911352129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52446090114526923940901419 78669135171790385911352129)
              ·
                refine ⟨59001851378842789433514097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 78669135171790385911352129 59001851378842789433514097)
                ·
                  refine ⟨44251388534132092075135573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 59001851378842789433514097 44251388534132092075135573)
                  ·
                    refine ⟨518570959384360454005495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 44251388534132092075135573 518570959384360454005495)
                    ·
                      rfl

theorem cell23_3029740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 8].length) (baseStart_3029740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3029740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3029740 prefixEnd_3029740 := by exact prefixLift 3029740
  have htrace : WordTrace (prefixWord ++ tailWord_3029740) baseStart_3029740 baseEnd_3029740 := by
    simpa [prefixWord, tailWord_3029740, baseEnd_3029740] using wordTrace_append hprefix tailTrace_3029740
  have hstable : (prefixWord ++ tailWord_3029740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3029740).length < 2 ^ (prefixWord ++ tailWord_3029740).sum := by decide
  have hdescent : baseEnd_3029740 < baseStart_3029740 := by decide
  rcases family_descends (prefixWord ++ tailWord_3029740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3029760 : List Nat := [2, 1, 1, 2, 1, 1, 2, 1, 3, 3, 6]
def baseStart_3029760 : Nat := 118140960795 + 3029760 * 2 ^ 59
def prefixEnd_3029760 : Nat := 4983230072969 + 3 ^ 40 * 3029760 * 2
def baseEnd_3029760 : Nat := 1555723147766171283766393

theorem tailTrace_3029760 : CollatzResearch.WordTrace tailWord_3029760 prefixEnd_3029760 1555723147766171283766393 := by
  unfold tailWord_3029760
  simp only [CollatzResearch.WordTrace]
  refine ⟨55252212751852218328731367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73669617002469624438308489 55252212751852218328731367)
  ·
    refine ⟨82878319127778327493097051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55252212751852218328731367 82878319127778327493097051)
    ·
      refine ⟨124317478691667491239645577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82878319127778327493097051 124317478691667491239645577)
      ·
        refine ⟨93238109018750618429734183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 124317478691667491239645577 93238109018750618429734183)
        ·
          refine ⟨139857163528125927644601275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93238109018750618429734183 139857163528125927644601275)
          ·
            refine ⟨209785745292188891466901913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 139857163528125927644601275 209785745292188891466901913)
            ·
              refine ⟨157339308969141668600176435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 209785745292188891466901913 157339308969141668600176435)
              ·
                refine ⟨236008963453712502900264653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 157339308969141668600176435 236008963453712502900264653)
                ·
                  refine ⟨88503361295142188587599245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 236008963453712502900264653 88503361295142188587599245)
                  ·
                    refine ⟨33188760485678320720349717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 88503361295142188587599245 33188760485678320720349717)
                    ·
                      refine ⟨1555723147766171283766393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 33188760485678320720349717 1555723147766171283766393)
                      ·
                        rfl

theorem cell23_3029760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 1, 3, 3, 6].length) (baseStart_3029760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3029760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3029760 prefixEnd_3029760 := by exact prefixLift 3029760
  have htrace : WordTrace (prefixWord ++ tailWord_3029760) baseStart_3029760 baseEnd_3029760 := by
    simpa [prefixWord, tailWord_3029760, baseEnd_3029760] using wordTrace_append hprefix tailTrace_3029760
  have hstable : (prefixWord ++ tailWord_3029760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3029760).length < 2 ^ (prefixWord ++ tailWord_3029760).sum := by decide
  have hdescent : baseEnd_3029760 < baseStart_3029760 := by decide
  rcases family_descends (prefixWord ++ tailWord_3029760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3029764 : List Nat := [2, 3, 2, 2, 1, 1, 1, 2, 1, 6, 2]
def baseStart_3029764 : Nat := 118140960795 + 3029764 * 2 ^ 59
def prefixEnd_3029764 : Nat := 4983230072969 + 3 ^ 40 * 3029764 * 2
def baseEnd_3029764 : Nat := 1555725201688789268116375

theorem tailTrace_3029764 : CollatzResearch.WordTrace tailWord_3029764 prefixEnd_3029764 1555725201688789268116375 := by
  unfold tailWord_3029764
  simp only [CollatzResearch.WordTrace]
  refine ⟨55252285697844972670304173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73669714263793296893738897 55252285697844972670304173)
  ·
    refine ⟨20719607136691864751364065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55252285697844972670304173 20719607136691864751364065)
    ·
      refine ⟨15539705352518898563523049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20719607136691864751364065 15539705352518898563523049)
      ·
        refine ⟨11654779014389173922642287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15539705352518898563523049 11654779014389173922642287)
        ·
          refine ⟨17482168521583760883963431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11654779014389173922642287 17482168521583760883963431)
          ·
            refine ⟨26223252782375641325945147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17482168521583760883963431 26223252782375641325945147)
            ·
              refine ⟨39334879173563461988917721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26223252782375641325945147 39334879173563461988917721)
              ·
                refine ⟨29501159380172596491688291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39334879173563461988917721 29501159380172596491688291)
                ·
                  refine ⟨44251739070258894737532437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29501159380172596491688291 44251739070258894737532437)
                  ·
                    refine ⟨2074300268918385690821833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 44251739070258894737532437 2074300268918385690821833)
                    ·
                      refine ⟨1555725201688789268116375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2074300268918385690821833 1555725201688789268116375)
                      ·
                        rfl

theorem cell23_3029764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 2, 1, 6, 2].length) (baseStart_3029764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3029764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3029764 prefixEnd_3029764 := by exact prefixLift 3029764
  have htrace : WordTrace (prefixWord ++ tailWord_3029764) baseStart_3029764 baseEnd_3029764 := by
    simpa [prefixWord, tailWord_3029764, baseEnd_3029764] using wordTrace_append hprefix tailTrace_3029764
  have hstable : (prefixWord ++ tailWord_3029764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3029764).length < 2 ^ (prefixWord ++ tailWord_3029764).sum := by decide
  have hdescent : baseEnd_3029764 < baseStart_3029764 := by decide
  rcases family_descends (prefixWord ++ tailWord_3029764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3029791 : List Nat := [1, 1, 2, 4, 2, 2, 2, 4, 1, 4]
def baseStart_3029791 : Nat := 118140960795 + 3029791 * 2 ^ 59
def prefixEnd_3029791 : Nat := 4983230072969 + 3 ^ 40 * 3029791 * 2
def baseEnd_3029791 : Nat := 518579688555486887492917

theorem tailTrace_3029791 : CollatzResearch.WordTrace tailWord_3029791 prefixEnd_3029791 518579688555486887492917 := by
  unfold tailWord_3029791
  simp only [CollatzResearch.WordTrace]
  refine ⟨110505556166592128951841227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73670370777728085967894151 110505556166592128951841227)
  ·
    refine ⟨165758334249888193427761841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110505556166592128951841227 165758334249888193427761841)
    ·
      refine ⟨124318750687416145070821381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 165758334249888193427761841 124318750687416145070821381)
      ·
        refine ⟨23309765753890527200779009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 124318750687416145070821381 23309765753890527200779009)
        ·
          refine ⟨17482324315417895400584257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23309765753890527200779009 17482324315417895400584257)
          ·
            refine ⟨13111743236563421550438193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17482324315417895400584257 13111743236563421550438193)
            ·
              refine ⟨9833807427422566162828645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13111743236563421550438193 9833807427422566162828645)
              ·
                refine ⟨1843838892641731155530371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9833807427422566162828645 1843838892641731155530371)
                ·
                  refine ⟨2765758338962596733295557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1843838892641731155530371 2765758338962596733295557)
                  ·
                    refine ⟨518579688555486887492917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2765758338962596733295557 518579688555486887492917)
                    ·
                      rfl

theorem cell23_3029791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 2, 4, 1, 4].length) (baseStart_3029791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3029791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3029791 prefixEnd_3029791 := by exact prefixLift 3029791
  have htrace : WordTrace (prefixWord ++ tailWord_3029791) baseStart_3029791 baseEnd_3029791 := by
    simpa [prefixWord, tailWord_3029791, baseEnd_3029791] using wordTrace_append hprefix tailTrace_3029791
  have hstable : (prefixWord ++ tailWord_3029791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3029791).length < 2 ^ (prefixWord ++ tailWord_3029791).sum := by decide
  have hdescent : baseEnd_3029791 < baseStart_3029791 := by decide
  rcases family_descends (prefixWord ++ tailWord_3029791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3029804 : List Nat := [2, 2, 1, 1, 1, 4, 5, 1, 6]
def baseStart_3029804 : Nat := 118140960795 + 3029804 * 2 ^ 59
def prefixEnd_3029804 : Nat := 4983230072969 + 3 ^ 40 * 3029804 * 2
def baseEnd_3029804 : Nat := 172860637879441012401799

theorem tailTrace_3029804 : CollatzResearch.WordTrace tailWord_3029804 prefixEnd_3029804 172860637879441012401799 := by
  unfold tailWord_3029804
  simp only [CollatzResearch.WordTrace]
  refine ⟨55253015157772516086032233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73670686877030021448042977 55253015157772516086032233)
  ·
    refine ⟨41439761368329387064524175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55253015157772516086032233 41439761368329387064524175)
    ·
      refine ⟨62159642052494080596786263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41439761368329387064524175 62159642052494080596786263)
      ·
        refine ⟨93239463078741120895179395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62159642052494080596786263 93239463078741120895179395)
        ·
          refine ⟨139859194618111681342769093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93239463078741120895179395 139859194618111681342769093)
          ·
            refine ⟨26223598990895940251769205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 139859194618111681342769093 26223598990895940251769205)
            ·
              refine ⟨2458462405396494398603363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 26223598990895940251769205 2458462405396494398603363)
              ·
                refine ⟨3687693608094741597905045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2458462405396494398603363 3687693608094741597905045)
                ·
                  refine ⟨172860637879441012401799, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3687693608094741597905045 172860637879441012401799)
                  ·
                    rfl

theorem cell23_3029804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 6].length) (baseStart_3029804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3029804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3029804 prefixEnd_3029804 := by exact prefixLift 3029804
  have htrace : WordTrace (prefixWord ++ tailWord_3029804) baseStart_3029804 baseEnd_3029804 := by
    simpa [prefixWord, tailWord_3029804, baseEnd_3029804] using wordTrace_append hprefix tailTrace_3029804
  have hstable : (prefixWord ++ tailWord_3029804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3029804).length < 2 ^ (prefixWord ++ tailWord_3029804).sum := by decide
  have hdescent : baseEnd_3029804 < baseStart_3029804 := by decide
  rcases family_descends (prefixWord ++ tailWord_3029804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3029824 : List Nat := [2, 1, 1, 2, 2, 1, 1, 2, 6, 3, 2]
def baseStart_3029824 : Nat := 118140960795 + 3029824 * 2 ^ 59
def prefixEnd_3029824 : Nat := 4983230072969 + 3 ^ 40 * 3029824 * 2
def baseEnd_3029824 : Nat := 1555756010528059033366099

theorem tailTrace_3029824 : CollatzResearch.WordTrace tailWord_3029824 prefixEnd_3029824 1555756010528059033366099 := by
  unfold tailWord_3029824
  simp only [CollatzResearch.WordTrace]
  refine ⟨55253379887736287793896263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73671173183648383725195017 55253379887736287793896263)
  ·
    refine ⟨82880069831604431690844395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55253379887736287793896263 82880069831604431690844395)
    ·
      refine ⟨124320104747406647536266593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82880069831604431690844395 124320104747406647536266593)
      ·
        refine ⟨93240078560554985652199945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 124320104747406647536266593 93240078560554985652199945)
        ·
          refine ⟨69930058920416239239149959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93240078560554985652199945 69930058920416239239149959)
          ·
            refine ⟨104895088380624358858724939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69930058920416239239149959 104895088380624358858724939)
            ·
              refine ⟨157342632570936538288087409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 104895088380624358858724939 157342632570936538288087409)
              ·
                refine ⟨118006974428202403716065557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 157342632570936538288087409 118006974428202403716065557)
                ·
                  refine ⟨5531576926321987674190573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 118006974428202403716065557 5531576926321987674190573)
                  ·
                    refine ⟨2074341347370745377821465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5531576926321987674190573 2074341347370745377821465)
                    ·
                      refine ⟨1555756010528059033366099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2074341347370745377821465 1555756010528059033366099)
                      ·
                        rfl

theorem cell23_3029824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 2, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 2, 6, 3, 2].length) (baseStart_3029824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3029824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3029824 prefixEnd_3029824 := by exact prefixLift 3029824
  have htrace : WordTrace (prefixWord ++ tailWord_3029824) baseStart_3029824 baseEnd_3029824 := by
    simpa [prefixWord, tailWord_3029824, baseEnd_3029824] using wordTrace_append hprefix tailTrace_3029824
  have hstable : (prefixWord ++ tailWord_3029824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3029824).length < 2 ^ (prefixWord ++ tailWord_3029824).sum := by decide
  have hdescent : baseEnd_3029824 < baseStart_3029824 := by decide
  rcases family_descends (prefixWord ++ tailWord_3029824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3029857 : List Nat := [1, 2, 3, 1, 1, 1, 2, 3, 3, 1, 5]
def baseStart_3029857 : Nat := 118140960795 + 3029857 * 2 ^ 59
def prefixEnd_3029857 : Nat := 4983230072969 + 3 ^ 40 * 3029857 * 2
def baseEnd_3029857 : Nat := 1555772955389657404253447

theorem tailTrace_3029857 : CollatzResearch.WordTrace tailWord_3029857 prefixEnd_3029857 1555772955389657404253447 := by
  unfold tailWord_3029857
  simp only [CollatzResearch.WordTrace]
  refine ⟨110507963384353022223743825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73671975589568681482495883 110507963384353022223743825)
  ·
    refine ⟨82880972538264766667807869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110507963384353022223743825 82880972538264766667807869)
    ·
      refine ⟨31080364701849287500427951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82880972538264766667807869 31080364701849287500427951)
      ·
        refine ⟨46620547052773931250641927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31080364701849287500427951 46620547052773931250641927)
        ·
          refine ⟨69930820579160896875962891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46620547052773931250641927 69930820579160896875962891)
          ·
            refine ⟨104896230868741345313944337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69930820579160896875962891 104896230868741345313944337)
            ·
              refine ⟨78672173151556008985458253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 104896230868741345313944337 78672173151556008985458253)
              ·
                refine ⟨29502064931833503369546845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 78672173151556008985458253 29502064931833503369546845)
                ·
                  refine ⟨11063274349437563763580067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29502064931833503369546845 11063274349437563763580067)
                  ·
                    refine ⟨16594911524156345645370101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11063274349437563763580067 16594911524156345645370101)
                    ·
                      refine ⟨1555772955389657404253447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16594911524156345645370101 1555772955389657404253447)
                      ·
                        rfl

theorem cell23_3029857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 3, 3, 1, 5].length) (baseStart_3029857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3029857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3029857 prefixEnd_3029857 := by exact prefixLift 3029857
  have htrace : WordTrace (prefixWord ++ tailWord_3029857) baseStart_3029857 baseEnd_3029857 := by
    simpa [prefixWord, tailWord_3029857, baseEnd_3029857] using wordTrace_append hprefix tailTrace_3029857
  have hstable : (prefixWord ++ tailWord_3029857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3029857).length < 2 ^ (prefixWord ++ tailWord_3029857).sum := by decide
  have hdescent : baseEnd_3029857 < baseStart_3029857 := by decide
  rcases family_descends (prefixWord ++ tailWord_3029857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3029867 : List Nat := [1, 1, 1, 1, 2, 2, 6, 1, 1, 1, 6]
def baseStart_3029867 : Nat := 118140960795 + 3029867 * 2 ^ 59
def prefixEnd_3029867 : Nat := 4983230072969 + 3 ^ 40 * 3029867 * 2
def baseEnd_3029867 : Nat := 1555778090196202365128401

theorem tailTrace_3029867 : CollatzResearch.WordTrace tailWord_3029867 prefixEnd_3029867 1555778090196202365128401 := by
  unfold tailWord_3029867
  simp only [CollatzResearch.WordTrace]
  refine ⟨110508328114316793931607855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73672218742877862621071903 110508328114316793931607855)
  ·
    refine ⟨165762492171475190897411783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110508328114316793931607855 165762492171475190897411783)
    ·
      refine ⟨248643738257212786346117675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165762492171475190897411783 248643738257212786346117675)
      ·
        refine ⟨372965607385819179519176513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 248643738257212786346117675 372965607385819179519176513)
        ·
          refine ⟨279724205539364384639382385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 372965607385819179519176513 279724205539364384639382385)
          ·
            refine ⟨209793154154523288479536789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 279724205539364384639382385 209793154154523288479536789)
            ·
              refine ⟨9834054100993279147478287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 209793154154523288479536789 9834054100993279147478287)
              ·
                refine ⟨14751081151489918721217431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9834054100993279147478287 14751081151489918721217431)
                ·
                  refine ⟨22126621727234878081826147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14751081151489918721217431 22126621727234878081826147)
                  ·
                    refine ⟨33189932590852317122739221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22126621727234878081826147 33189932590852317122739221)
                    ·
                      refine ⟨1555778090196202365128401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 33189932590852317122739221 1555778090196202365128401)
                      ·
                        rfl

theorem cell23_3029867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 6, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 6, 1, 1, 1, 6].length) (baseStart_3029867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3029867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3029867 prefixEnd_3029867 := by exact prefixLift 3029867
  have htrace : WordTrace (prefixWord ++ tailWord_3029867) baseStart_3029867 baseEnd_3029867 := by
    simpa [prefixWord, tailWord_3029867, baseEnd_3029867] using wordTrace_append hprefix tailTrace_3029867
  have hstable : (prefixWord ++ tailWord_3029867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3029867).length < 2 ^ (prefixWord ++ tailWord_3029867).sum := by decide
  have hdescent : baseEnd_3029867 < baseStart_3029867 := by decide
  rcases family_descends (prefixWord ++ tailWord_3029867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3029871 : List Nat := [1, 1, 2, 1, 3, 1, 1, 6, 3, 2, 2]
def baseStart_3029871 : Nat := 118140960795 + 3029871 * 2 ^ 59
def prefixEnd_3029871 : Nat := 4983230072969 + 3 ^ 40 * 3029871 * 2
def baseEnd_3029871 : Nat := 1555780144118820349478383

theorem tailTrace_3029871 : CollatzResearch.WordTrace tailWord_3029871 prefixEnd_3029871 1555780144118820349478383 := by
  unfold tailWord_3029871
  simp only [CollatzResearch.WordTrace]
  refine ⟨110508474006302302614753467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73672316004201535076502311 110508474006302302614753467)
  ·
    refine ⟨165762711009453453922130201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110508474006302302614753467 165762711009453453922130201)
    ·
      refine ⟨124322033257090090441597651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 165762711009453453922130201 124322033257090090441597651)
      ·
        refine ⟨186483049885635135662396477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124322033257090090441597651 186483049885635135662396477)
        ·
          refine ⟨69931143707113175873398679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 186483049885635135662396477 69931143707113175873398679)
          ·
            refine ⟨104896715560669763810098019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69931143707113175873398679 104896715560669763810098019)
            ·
              refine ⟨157345073341004645715147029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 104896715560669763810098019 157345073341004645715147029)
              ·
                refine ⟨7375550312859592767897517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 157345073341004645715147029 7375550312859592767897517)
                ·
                  refine ⟨2765831367322347287961569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7375550312859592767897517 2765831367322347287961569)
                  ·
                    refine ⟨2074373525491760465971177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2765831367322347287961569 2074373525491760465971177)
                    ·
                      refine ⟨1555780144118820349478383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2074373525491760465971177 1555780144118820349478383)
                      ·
                        rfl

theorem cell23_3029871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 6, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 6, 3, 2, 2].length) (baseStart_3029871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3029871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3029871 prefixEnd_3029871 := by exact prefixLift 3029871
  have htrace : WordTrace (prefixWord ++ tailWord_3029871) baseStart_3029871 baseEnd_3029871 := by
    simpa [prefixWord, tailWord_3029871, baseEnd_3029871] using wordTrace_append hprefix tailTrace_3029871
  have hstable : (prefixWord ++ tailWord_3029871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3029871).length < 2 ^ (prefixWord ++ tailWord_3029871).sum := by decide
  have hdescent : baseEnd_3029871 < baseStart_3029871 := by decide
  rcases family_descends (prefixWord ++ tailWord_3029871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3029898 : List Nat := [3, 1, 2, 4, 1, 2, 2, 2, 2, 4]
def baseStart_3029898 : Nat := 118140960795 + 3029898 * 2 ^ 59
def prefixEnd_3029898 : Nat := 4983230072969 + 3 ^ 40 * 3029898 * 2
def baseEnd_3029898 : Nat := 518598002698830581280253

theorem tailTrace_3029898 : CollatzResearch.WordTrace tailWord_3029898 prefixEnd_3029898 518598002698830581280253 := by
  unfold tailWord_3029898
  simp only [CollatzResearch.WordTrace]
  refine ⟨27627364694301121556496587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73672972518136324150657565 27627364694301121556496587)
  ·
    refine ⟨41441047041451682334744881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27627364694301121556496587 41441047041451682334744881)
    ·
      refine ⟨31080785281088761751058661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41441047041451682334744881 31080785281088761751058661)
      ·
        refine ⟨5827647240204142828323499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31080785281088761751058661 5827647240204142828323499)
        ·
          refine ⟨8741470860306214242485249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5827647240204142828323499 8741470860306214242485249)
          ·
            refine ⟨6556103145229660681863937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8741470860306214242485249 6556103145229660681863937)
            ·
              refine ⟨4917077358922245511397953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6556103145229660681863937 4917077358922245511397953)
              ·
                refine ⟨3687808019191684133548465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4917077358922245511397953 3687808019191684133548465)
                ·
                  refine ⟨2765856014393763100161349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3687808019191684133548465 2765856014393763100161349)
                  ·
                    refine ⟨518598002698830581280253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2765856014393763100161349 518598002698830581280253)
                    ·
                      rfl

theorem cell23_3029898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 2, 2, 2, 4].length) (baseStart_3029898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3029898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3029898 prefixEnd_3029898 := by exact prefixLift 3029898
  have htrace : WordTrace (prefixWord ++ tailWord_3029898) baseStart_3029898 baseEnd_3029898 := by
    simpa [prefixWord, tailWord_3029898, baseEnd_3029898] using wordTrace_append hprefix tailTrace_3029898
  have hstable : (prefixWord ++ tailWord_3029898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3029898).length < 2 ^ (prefixWord ++ tailWord_3029898).sum := by decide
  have hdescent : baseEnd_3029898 < baseStart_3029898 := by decide
  rcases family_descends (prefixWord ++ tailWord_3029898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3029921 : List Nat := [1, 2, 3, 4, 1, 1, 1, 3, 1, 3, 3]
def baseStart_3029921 : Nat := 118140960795 + 3029921 * 2 ^ 59
def prefixEnd_3029921 : Nat := 4983230072969 + 3 ^ 40 * 3029921 * 2
def baseEnd_3029921 : Nat := 1555805818151545153853153

theorem tailTrace_3029921 : CollatzResearch.WordTrace tailWord_3029921 prefixEnd_3029921 1555805818151545153853153 := by
  unfold tailWord_3029921
  simp only [CollatzResearch.WordTrace]
  refine ⟨110510297656121161154073617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73673531770747440769382411 110510297656121161154073617)
  ·
    refine ⟨82882723242090870865555213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110510297656121161154073617 82882723242090870865555213)
    ·
      refine ⟨31081021215784076574583205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82882723242090870865555213 31081021215784076574583205)
      ·
        refine ⟨5827691477959514357734351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31081021215784076574583205 5827691477959514357734351)
        ·
          refine ⟨8741537216939271536601527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5827691477959514357734351 8741537216939271536601527)
          ·
            refine ⟨13112305825408907304902291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8741537216939271536601527 13112305825408907304902291)
            ·
              refine ⟨19668458738113360957353437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13112305825408907304902291 19668458738113360957353437)
              ·
                refine ⟨7375672026792510359007539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19668458738113360957353437 7375672026792510359007539)
                ·
                  refine ⟨11063508040188765538511309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7375672026792510359007539 11063508040188765538511309)
                  ·
                    refine ⟨4148815515070787076941741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11063508040188765538511309 4148815515070787076941741)
                    ·
                      refine ⟨1555805818151545153853153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4148815515070787076941741 1555805818151545153853153)
                      ·
                        rfl

theorem cell23_3029921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 1, 3, 1, 3, 3].length) (baseStart_3029921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3029921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3029921 prefixEnd_3029921 := by exact prefixLift 3029921
  have htrace : WordTrace (prefixWord ++ tailWord_3029921) baseStart_3029921 baseEnd_3029921 := by
    simpa [prefixWord, tailWord_3029921, baseEnd_3029921] using wordTrace_append hprefix tailTrace_3029921
  have hstable : (prefixWord ++ tailWord_3029921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3029921).length < 2 ^ (prefixWord ++ tailWord_3029921).sum := by decide
  have hdescent : baseEnd_3029921 < baseStart_3029921 := by decide
  rcases family_descends (prefixWord ++ tailWord_3029921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3029978 : List Nat := [3, 1, 1, 2, 4, 1, 3, 1, 1, 4, 2]
def baseStart_3029978 : Nat := 118140960795 + 3029978 * 2 ^ 59
def prefixEnd_3029978 : Nat := 4983230072969 + 3 ^ 40 * 3029978 * 2
def baseEnd_3029978 : Nat := 1555835086548851430840391

theorem tailTrace_3029978 : CollatzResearch.WordTrace tailWord_3029978 prefixEnd_3029978 1555835086548851430840391 := by
  unfold tailWord_3029978
  simp only [CollatzResearch.WordTrace]
  refine ⟨27628094154228664972224647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73674917744609773259265725 27628094154228664972224647)
  ·
    refine ⟨41442141231342997458336971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27628094154228664972224647 41442141231342997458336971)
    ·
      refine ⟨62163211847014496187505457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41442141231342997458336971 62163211847014496187505457)
      ·
        refine ⟨46622408885260872140629093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62163211847014496187505457 46622408885260872140629093)
        ·
          refine ⟨8741701665986413526367955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 46622408885260872140629093 8741701665986413526367955)
          ·
            refine ⟨13112552498979620289551933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8741701665986413526367955 13112552498979620289551933)
            ·
              refine ⟨4917207187117357608581975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13112552498979620289551933 4917207187117357608581975)
              ·
                refine ⟨7375810780676036412872963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4917207187117357608581975 7375810780676036412872963)
                ·
                  refine ⟨11063716171014054619309445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7375810780676036412872963 11063716171014054619309445)
                  ·
                    refine ⟨2074446782065135241120521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11063716171014054619309445 2074446782065135241120521)
                    ·
                      refine ⟨1555835086548851430840391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2074446782065135241120521 1555835086548851430840391)
                      ·
                        rfl

theorem cell23_3029978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 3, 1, 1, 4, 2].length) (baseStart_3029978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3029978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3029978 prefixEnd_3029978 := by exact prefixLift 3029978
  have htrace : WordTrace (prefixWord ++ tailWord_3029978) baseStart_3029978 baseEnd_3029978 := by
    simpa [prefixWord, tailWord_3029978, baseEnd_3029978] using wordTrace_append hprefix tailTrace_3029978
  have hstable : (prefixWord ++ tailWord_3029978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3029978).length < 2 ^ (prefixWord ++ tailWord_3029978).sum := by decide
  have hdescent : baseEnd_3029978 < baseStart_3029978 := by decide
  rcases family_descends (prefixWord ++ tailWord_3029978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3030021 : List Nat := [1, 3, 1, 1, 2, 3, 2, 1, 2, 5, 2]
def baseStart_3030021 : Nat := 118140960795 + 3030021 * 2 ^ 59
def prefixEnd_3030021 : Nat := 4983230072969 + 3 ^ 40 * 3030021 * 2
def baseEnd_3030021 : Nat := 1555857166216994762602693

theorem tailTrace_3030021 : CollatzResearch.WordTrace tailWord_3030021 prefixEnd_3030021 1555857166216994762602693 := by
  unfold tailWord_3030021
  simp only [CollatzResearch.WordTrace]
  refine ⟨110513944955758878232713917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73675963303839252155142611 110513944955758878232713917)
  ·
    refine ⟨41442729358409579337267719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 110513944955758878232713917 41442729358409579337267719)
    ·
      refine ⟨62164094037614369005901579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41442729358409579337267719 62164094037614369005901579)
      ·
        refine ⟨93246141056421553508852369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62164094037614369005901579 93246141056421553508852369)
        ·
          refine ⟨69934605792316165131639277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93246141056421553508852369 69934605792316165131639277)
          ·
            refine ⟨26225477172118561924364729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 69934605792316165131639277 26225477172118561924364729)
            ·
              refine ⟨19669107879088921443273547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26225477172118561924364729 19669107879088921443273547)
              ·
                refine ⟨29503661818633382164910321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19669107879088921443273547 29503661818633382164910321)
                ·
                  refine ⟨22127746363975036623682741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29503661818633382164910321 22127746363975036623682741)
                  ·
                    refine ⟨2074476221622659683470257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 22127746363975036623682741 2074476221622659683470257)
                    ·
                      refine ⟨1555857166216994762602693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2074476221622659683470257 1555857166216994762602693)
                      ·
                        rfl

theorem cell23_3030021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 2, 1, 2, 5, 2].length) (baseStart_3030021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3030021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3030021 prefixEnd_3030021 := by exact prefixLift 3030021
  have htrace : WordTrace (prefixWord ++ tailWord_3030021) baseStart_3030021 baseEnd_3030021 := by
    simpa [prefixWord, tailWord_3030021, baseEnd_3030021] using wordTrace_append hprefix tailTrace_3030021
  have hstable : (prefixWord ++ tailWord_3030021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3030021).length < 2 ^ (prefixWord ++ tailWord_3030021).sum := by decide
  have hdescent : baseEnd_3030021 < baseStart_3030021 := by decide
  rcases family_descends (prefixWord ++ tailWord_3030021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3030024 : List Nat := [2, 1, 3, 2, 1, 3, 1, 1, 1, 1, 7]
def baseStart_3030024 : Nat := 118140960795 + 3030024 * 2 ^ 59
def prefixEnd_3030024 : Nat := 4983230072969 + 3 ^ 40 * 3030024 * 2
def baseEnd_3030024 : Nat := 1555858706658958250865179

theorem tailTrace_3030024 : CollatzResearch.WordTrace tailWord_3030024 prefixEnd_3030024 1555858706658958250865179 := by
  unfold tailWord_3030024
  simp only [CollatzResearch.WordTrace]
  refine ⟨55257027187374004872536563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73676036249832006496715417 55257027187374004872536563)
  ·
    refine ⟨82885540781061007308804845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55257027187374004872536563 82885540781061007308804845)
    ·
      refine ⟨31082077792897877740801817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82885540781061007308804845 31082077792897877740801817)
      ·
        refine ⟨23311558344673408305601363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31082077792897877740801817 23311558344673408305601363)
        ·
          refine ⟨34967337517010112458402045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23311558344673408305601363 34967337517010112458402045)
          ·
            refine ⟨13112751568878792171900767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34967337517010112458402045 13112751568878792171900767)
            ·
              refine ⟨19669127353318188257851151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13112751568878792171900767 19669127353318188257851151)
              ·
                refine ⟨29503691029977282386776727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19669127353318188257851151 29503691029977282386776727)
                ·
                  refine ⟨44255536544965923580165091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29503691029977282386776727 44255536544965923580165091)
                  ·
                    refine ⟨66383304817448885370247637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 44255536544965923580165091 66383304817448885370247637)
                    ·
                      refine ⟨1555858706658958250865179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 66383304817448885370247637 1555858706658958250865179)
                      ·
                        rfl

theorem cell23_3030024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 1, 1, 1, 1, 7].length) (baseStart_3030024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3030024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3030024 prefixEnd_3030024 := by exact prefixLift 3030024
  have htrace : WordTrace (prefixWord ++ tailWord_3030024) baseStart_3030024 baseEnd_3030024 := by
    simpa [prefixWord, tailWord_3030024, baseEnd_3030024] using wordTrace_append hprefix tailTrace_3030024
  have hstable : (prefixWord ++ tailWord_3030024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3030024).length < 2 ^ (prefixWord ++ tailWord_3030024).sum := by decide
  have hdescent : baseEnd_3030024 < baseStart_3030024 := by decide
  rcases family_descends (prefixWord ++ tailWord_3030024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3030051 : List Nat := [1, 1, 1, 4, 3, 2, 1, 3, 2, 1, 4]
def baseStart_3030051 : Nat := 118140960795 + 3030051 * 2 ^ 59
def prefixEnd_3030051 : Nat := 4983230072969 + 3 ^ 40 * 3030051 * 2
def baseEnd_3030051 : Nat := 1555872570636629645227555

theorem tailTrace_3030051 : CollatzResearch.WordTrace tailWord_3030051 prefixEnd_3030051 1555872570636629645227555 := by
  unfold tailWord_3030051
  simp only [CollatzResearch.WordTrace]
  refine ⟨110515039145650193356306007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73676692763766795570870671 110515039145650193356306007)
  ·
    refine ⟨165772558718475290034459011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110515039145650193356306007 165772558718475290034459011)
    ·
      refine ⟨248658838077712935051688517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165772558718475290034459011 248658838077712935051688517)
      ·
        refine ⟨46623532139571175322191597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 248658838077712935051688517 46623532139571175322191597)
        ·
          refine ⟨17483824552339190745821849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46623532139571175322191597 17483824552339190745821849)
          ·
            refine ⟨13112868414254393059366387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17483824552339190745821849 13112868414254393059366387)
            ·
              refine ⟨19669302621381589589049581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13112868414254393059366387 19669302621381589589049581)
              ·
                refine ⟨7375988483018096095893593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19669302621381589589049581 7375988483018096095893593)
                ·
                  refine ⟨5531991362263572071920195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7375988483018096095893593 5531991362263572071920195)
                  ·
                    refine ⟨8297987043395358107880293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5531991362263572071920195 8297987043395358107880293)
                    ·
                      refine ⟨1555872570636629645227555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8297987043395358107880293 1555872570636629645227555)
                      ·
                        rfl

theorem cell23_3030051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 1, 3, 2, 1, 4].length) (baseStart_3030051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3030051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3030051 prefixEnd_3030051 := by exact prefixLift 3030051
  have htrace : WordTrace (prefixWord ++ tailWord_3030051) baseStart_3030051 baseEnd_3030051 := by
    simpa [prefixWord, tailWord_3030051, baseEnd_3030051] using wordTrace_append hprefix tailTrace_3030051
  have hstable : (prefixWord ++ tailWord_3030051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3030051).length < 2 ^ (prefixWord ++ tailWord_3030051).sum := by decide
  have hdescent : baseEnd_3030051 < baseStart_3030051 := by decide
  rcases family_descends (prefixWord ++ tailWord_3030051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3030064 : List Nat := [2, 1, 1, 1, 2, 4, 2, 1, 2, 1, 6]
def baseStart_3030064 : Nat := 118140960795 + 3030064 * 2 ^ 59
def prefixEnd_3030064 : Nat := 4983230072969 + 3 ^ 40 * 3030064 * 2
def baseEnd_3030064 : Nat := 1555879245885138094364995

theorem tailTrace_3030064 : CollatzResearch.WordTrace tailWord_3030064 prefixEnd_3030064 1555879245885138094364995 := by
  unfold tailWord_3030064
  simp only [CollatzResearch.WordTrace]
  refine ⟨55257756647301548288264623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73677008863068731051019497 55257756647301548288264623)
  ·
    refine ⟨82886634970952322432396935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55257756647301548288264623 82886634970952322432396935)
    ·
      refine ⟨124329952456428483648595403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82886634970952322432396935 124329952456428483648595403)
      ·
        refine ⟨186494928684642725472893105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124329952456428483648595403 186494928684642725472893105)
        ·
          refine ⟨139871196513482044104669829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 186494928684642725472893105 139871196513482044104669829)
          ·
            refine ⟨26225849346277883269625593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 139871196513482044104669829 26225849346277883269625593)
            ·
              refine ⟨19669387009708412452219195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26225849346277883269625593 19669387009708412452219195)
              ·
                refine ⟨29504080514562618678328793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19669387009708412452219195 29504080514562618678328793)
                ·
                  refine ⟨22128060385921964008746595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29504080514562618678328793 22128060385921964008746595)
                  ·
                    refine ⟨33192090578882946013119893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22128060385921964008746595 33192090578882946013119893)
                    ·
                      refine ⟨1555879245885138094364995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 33192090578882946013119893 1555879245885138094364995)
                      ·
                        rfl

theorem cell23_3030064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 2, 1, 2, 1, 6].length) (baseStart_3030064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3030064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3030064 prefixEnd_3030064 := by exact prefixLift 3030064
  have htrace : WordTrace (prefixWord ++ tailWord_3030064) baseStart_3030064 baseEnd_3030064 := by
    simpa [prefixWord, tailWord_3030064, baseEnd_3030064] using wordTrace_append hprefix tailTrace_3030064
  have hstable : (prefixWord ++ tailWord_3030064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3030064).length < 2 ^ (prefixWord ++ tailWord_3030064).sum := by decide
  have hdescent : baseEnd_3030064 < baseStart_3030064 := by decide
  rcases family_descends (prefixWord ++ tailWord_3030064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3030074 : List Nat := [3, 1, 1, 1, 3, 1, 2, 3, 8]
def baseStart_3030074 : Nat := 118140960795 + 3030074 * 2 ^ 59
def prefixEnd_3030074 : Nat := 4983230072969 + 3 ^ 40 * 3030074 * 2
def baseEnd_3030074 : Nat := 172876042299075895026661

theorem tailTrace_3030074 : CollatzResearch.WordTrace tailWord_3030074 prefixEnd_3030074 172876042299075895026661 := by
  unfold tailWord_3030074
  simp only [CollatzResearch.WordTrace]
  refine ⟨27628969506141717071098319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73677252016377912189595517 27628969506141717071098319)
  ·
    refine ⟨41443454259212575606647479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27628969506141717071098319 41443454259212575606647479)
    ·
      refine ⟨62165181388818863409971219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41443454259212575606647479 62165181388818863409971219)
      ·
        refine ⟨93247772083228295114956829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62165181388818863409971219 93247772083228295114956829)
        ·
          refine ⟨34967914531210610668108811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 93247772083228295114956829 34967914531210610668108811)
          ·
            refine ⟨52451871796815916002163217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34967914531210610668108811 52451871796815916002163217)
            ·
              refine ⟨39338903847611937001622413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52451871796815916002163217 39338903847611937001622413)
              ·
                refine ⟨14752088942854476375608405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39338903847611937001622413 14752088942854476375608405)
                ·
                  refine ⟨172876042299075895026661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 14752088942854476375608405 172876042299075895026661)
                  ·
                    rfl

theorem cell23_3030074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 3, 8].length) (baseStart_3030074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3030074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3030074 prefixEnd_3030074 := by exact prefixLift 3030074
  have htrace : WordTrace (prefixWord ++ tailWord_3030074) baseStart_3030074 baseEnd_3030074 := by
    simpa [prefixWord, tailWord_3030074, baseEnd_3030074] using wordTrace_append hprefix tailTrace_3030074
  have hstable : (prefixWord ++ tailWord_3030074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3030074).length < 2 ^ (prefixWord ++ tailWord_3030074).sum := by decide
  have hdescent : baseEnd_3030074 < baseStart_3030074 := by decide
  rcases family_descends (prefixWord ++ tailWord_3030074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3030128 : List Nat := [2, 1, 1, 1, 5, 1, 2, 1, 4, 3, 2]
def baseStart_3030128 : Nat := 118140960795 + 3030128 * 2 ^ 59
def prefixEnd_3030128 : Nat := 4983230072969 + 3 ^ 40 * 3030128 * 2
def baseEnd_3030128 : Nat := 1555912108647025843964701

theorem tailTrace_3030128 : CollatzResearch.WordTrace tailWord_3030128 prefixEnd_3030128 1555912108647025843964701 := by
  unfold tailWord_3030128
  simp only [CollatzResearch.WordTrace]
  refine ⟨55258923783185617753429519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73678565044247490337906025 55258923783185617753429519)
  ·
    refine ⟨82888385674778426630144279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55258923783185617753429519 82888385674778426630144279)
    ·
      refine ⟨124332578512167639945216419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82888385674778426630144279 124332578512167639945216419)
      ·
        refine ⟨186498867768251459917824629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124332578512167639945216419 186498867768251459917824629)
        ·
          refine ⟨17484268853273574367296059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 186498867768251459917824629 17484268853273574367296059)
          ·
            refine ⟨26226403279910361550944089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17484268853273574367296059 26226403279910361550944089)
            ·
              refine ⟨19669802459932771163208067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26226403279910361550944089 19669802459932771163208067)
              ·
                refine ⟨29504703689899156744812101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19669802459932771163208067 29504703689899156744812101)
                ·
                  refine ⟨5532131941856091889652269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29504703689899156744812101 5532131941856091889652269)
                  ·
                    refine ⟨2074549478196034458619601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5532131941856091889652269 2074549478196034458619601)
                    ·
                      refine ⟨1555912108647025843964701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2074549478196034458619601 1555912108647025843964701)
                      ·
                        rfl

theorem cell23_3030128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 2, 1, 4, 3, 2].length) (baseStart_3030128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3030128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3030128 prefixEnd_3030128 := by exact prefixLift 3030128
  have htrace : WordTrace (prefixWord ++ tailWord_3030128) baseStart_3030128 baseEnd_3030128 := by
    simpa [prefixWord, tailWord_3030128, baseEnd_3030128] using wordTrace_append hprefix tailTrace_3030128
  have hstable : (prefixWord ++ tailWord_3030128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3030128).length < 2 ^ (prefixWord ++ tailWord_3030128).sum := by decide
  have hdescent : baseEnd_3030128 < baseStart_3030128 := by decide
  rcases family_descends (prefixWord ++ tailWord_3030128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3030135 : List Nat := [1, 1, 3, 1, 1, 4, 1, 6, 1, 1, 3]
def baseStart_3030135 : Nat := 118140960795 + 3030135 * 2 ^ 59
def prefixEnd_3030135 : Nat := 4983230072969 + 3 ^ 40 * 3030135 * 2
def baseEnd_3030135 : Nat := 1555915703011607316577169

theorem tailTrace_3030135 : CollatzResearch.WordTrace tailWord_3030135 prefixEnd_3030135 1555915703011607316577169 := by
  unfold tailWord_3030135
  simp only [CollatzResearch.WordTrace]
  refine ⟨110518102877345875702363859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73678735251563917134909239 110518102877345875702363859)
  ·
    refine ⟨165777154316018813553545789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110518102877345875702363859 165777154316018813553545789)
    ·
      refine ⟨62166432868507055082579671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 165777154316018813553545789 62166432868507055082579671)
      ·
        refine ⟨93249649302760582623869507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62166432868507055082579671 93249649302760582623869507)
        ·
          refine ⟨139874473954140873935804261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93249649302760582623869507 139874473954140873935804261)
          ·
            refine ⟨26226463866401413862963299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 139874473954140873935804261 26226463866401413862963299)
            ·
              refine ⟨39339695799602120794444949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26226463866401413862963299 39339695799602120794444949)
              ·
                refine ⟨1844048240606349412239607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 39339695799602120794444949 1844048240606349412239607)
                ·
                  refine ⟨2766072360909524118359411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1844048240606349412239607 2766072360909524118359411)
                  ·
                    refine ⟨4149108541364286177539117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2766072360909524118359411 4149108541364286177539117)
                    ·
                      refine ⟨1555915703011607316577169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4149108541364286177539117 1555915703011607316577169)
                      ·
                        rfl

theorem cell23_3030135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 6, 1, 1, 3].length) (baseStart_3030135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3030135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3030135 prefixEnd_3030135 := by exact prefixLift 3030135
  have htrace : WordTrace (prefixWord ++ tailWord_3030135) baseStart_3030135 baseEnd_3030135 := by
    simpa [prefixWord, tailWord_3030135, baseEnd_3030135] using wordTrace_append hprefix tailTrace_3030135
  have hstable : (prefixWord ++ tailWord_3030135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3030135).length < 2 ^ (prefixWord ++ tailWord_3030135).sum := by decide
  have hdescent : baseEnd_3030135 < baseStart_3030135 := by decide
  rcases family_descends (prefixWord ++ tailWord_3030135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3030168 : List Nat := [2, 1, 2, 4, 2, 1, 1, 2, 4, 4]
def baseStart_3030168 : Nat := 118140960795 + 3030168 * 2 ^ 59
def prefixEnd_3030168 : Nat := 4983230072969 + 3 ^ 40 * 3030168 * 2
def baseEnd_3030168 : Nat := 518644215957735229154839

theorem tailTrace_3030168 : CollatzResearch.WordTrace tailWord_3030168 prefixEnd_3030168 518644215957735229154839 := by
  unfold tailWord_3030168
  simp only [CollatzResearch.WordTrace]
  refine ⟨55259653243113161169157579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73679537657484214892210105 55259653243113161169157579)
  ·
    refine ⟨82889479864669741753736369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55259653243113161169157579 82889479864669741753736369)
    ·
      refine ⟨62167109898502306315302277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82889479864669741753736369 62167109898502306315302277)
      ·
        refine ⟨11656333105969182434119177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 62167109898502306315302277 11656333105969182434119177)
        ·
          refine ⟨8742249829476886825589383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11656333105969182434119177 8742249829476886825589383)
          ·
            refine ⟨13113374744215330238384075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8742249829476886825589383 13113374744215330238384075)
            ·
              refine ⟨19670062116322995357576113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13113374744215330238384075 19670062116322995357576113)
              ·
                refine ⟨14752546587242246518182085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19670062116322995357576113 14752546587242246518182085)
                ·
                  refine ⟨2766102485107921222159141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14752546587242246518182085 2766102485107921222159141)
                  ·
                    refine ⟨518644215957735229154839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2766102485107921222159141 518644215957735229154839)
                    ·
                      rfl

theorem cell23_3030168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 1, 2, 4, 4].length) (baseStart_3030168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3030168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3030168 prefixEnd_3030168 := by exact prefixLift 3030168
  have htrace : WordTrace (prefixWord ++ tailWord_3030168) baseStart_3030168 baseEnd_3030168 := by
    simpa [prefixWord, tailWord_3030168, baseEnd_3030168] using wordTrace_append hprefix tailTrace_3030168
  have hstable : (prefixWord ++ tailWord_3030168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3030168).length < 2 ^ (prefixWord ++ tailWord_3030168).sum := by decide
  have hdescent : baseEnd_3030168 < baseStart_3030168 := by decide
  rcases family_descends (prefixWord ++ tailWord_3030168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3030181 : List Nat := [1, 3, 1, 2, 1, 6, 9]
def baseStart_3030181 : Nat := 118140960795 + 3030181 * 2 ^ 59
def prefixEnd_3030181 : Nat := 4983230072969 + 3 ^ 40 * 3030181 * 2
def baseEnd_3030181 : Nat := 19209127445947088106197

theorem tailTrace_3030181 : CollatzResearch.WordTrace tailWord_3030181 prefixEnd_3030181 19209127445947088106197 := by
  unfold tailWord_3030181
  simp only [CollatzResearch.WordTrace]
  refine ⟨110519780635179225558538397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73679853756786150372358931 110519780635179225558538397)
  ·
    refine ⟨41444917738192209584451899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 110519780635179225558538397 41444917738192209584451899)
    ·
      refine ⟨62167376607288314376677849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41444917738192209584451899 62167376607288314376677849)
      ·
        refine ⟨46625532455466235782508387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62167376607288314376677849 46625532455466235782508387)
        ·
          refine ⟨69938298683199353673762581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46625532455466235782508387 69938298683199353673762581)
          ·
            refine ⟨3278357750774969703457621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 69938298683199353673762581 3278357750774969703457621)
            ·
              refine ⟨19209127445947088106197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3278357750774969703457621 19209127445947088106197)
              ·
                rfl

theorem cell23_3030181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 6, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 6, 9].length) (baseStart_3030181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3030181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3030181 prefixEnd_3030181 := by exact prefixLift 3030181
  have htrace : WordTrace (prefixWord ++ tailWord_3030181) baseStart_3030181 baseEnd_3030181 := by
    simpa [prefixWord, tailWord_3030181, baseEnd_3030181] using wordTrace_append hprefix tailTrace_3030181
  have hstable : (prefixWord ++ tailWord_3030181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3030181).length < 2 ^ (prefixWord ++ tailWord_3030181).sum := by decide
  have hdescent : baseEnd_3030181 < baseStart_3030181 := by decide
  rcases family_descends (prefixWord ++ tailWord_3030181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3030186 : List Nat := [3, 1, 5, 1, 1, 2, 3, 2, 1, 1, 3]
def baseStart_3030186 : Nat := 118140960795 + 3030186 * 2 ^ 59
def prefixEnd_3030186 : Nat := 4983230072969 + 3 ^ 40 * 3030186 * 2
def baseEnd_3030186 : Nat := 1555941890524986617039435

theorem tailTrace_3030186 : CollatzResearch.WordTrace tailWord_3030186 prefixEnd_3030186 1555941890524986617039435 := by
  unfold tailWord_3030186
  simp only [CollatzResearch.WordTrace]
  refine ⟨27629990750040277853117603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73679975333440740941646941 27629990750040277853117603)
  ·
    refine ⟨41444986125060416779676405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27629990750040277853117603 41444986125060416779676405)
    ·
      refine ⟨3885467449224414073094663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 41444986125060416779676405 3885467449224414073094663)
      ·
        refine ⟨5828201173836621109641995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3885467449224414073094663 5828201173836621109641995)
        ·
          refine ⟨8742301760754931664462993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5828201173836621109641995 8742301760754931664462993)
          ·
            refine ⟨6556726320566198748347245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8742301760754931664462993 6556726320566198748347245)
            ·
              refine ⟨2458772370212324530630217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6556726320566198748347245 2458772370212324530630217)
              ·
                refine ⟨1844079277659243397972663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2458772370212324530630217 1844079277659243397972663)
                ·
                  refine ⟨2766118916488865096958995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1844079277659243397972663 2766118916488865096958995)
                  ·
                    refine ⟨4149178374733297645438493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2766118916488865096958995 4149178374733297645438493)
                    ·
                      refine ⟨1555941890524986617039435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4149178374733297645438493 1555941890524986617039435)
                      ·
                        rfl

theorem cell23_3030186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 3, 2, 1, 1, 3].length) (baseStart_3030186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3030186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3030186 prefixEnd_3030186 := by exact prefixLift 3030186
  have htrace : WordTrace (prefixWord ++ tailWord_3030186) baseStart_3030186 baseEnd_3030186 := by
    simpa [prefixWord, tailWord_3030186, baseEnd_3030186] using wordTrace_append hprefix tailTrace_3030186
  have hstable : (prefixWord ++ tailWord_3030186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3030186).length < 2 ^ (prefixWord ++ tailWord_3030186).sum := by decide
  have hdescent : baseEnd_3030186 < baseStart_3030186 := by decide
  rcases family_descends (prefixWord ++ tailWord_3030186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3030265 : List Nat := [1, 2, 1, 3, 1, 1, 6, 1, 1, 4, 2]
def baseStart_3030265 : Nat := 118140960795 + 3030265 * 2 ^ 59
def prefixEnd_3030265 : Nat := 4983230072969 + 3 ^ 40 * 3030265 * 2
def baseEnd_3030265 : Nat := 1555982455496691807951571

theorem tailTrace_3030265 : CollatzResearch.WordTrace tailWord_3030265 prefixEnd_3030265 1555982455496691807951571 := by
  unfold tailWord_3030265
  simp only [CollatzResearch.WordTrace]
  refine ⟨110522844366874907904596249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73681896244583271936397499 110522844366874907904596249)
  ·
    refine ⟨82892133275156180928447187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110522844366874907904596249 82892133275156180928447187)
    ·
      refine ⟨124338199912734271392670781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82892133275156180928447187 124338199912734271392670781)
      ·
        refine ⟨46626824967275351772251543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 124338199912734271392670781 46626824967275351772251543)
        ·
          refine ⟨69940237450913027658377315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46626824967275351772251543 69940237450913027658377315)
          ·
            refine ⟨104910356176369541487565973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69940237450913027658377315 104910356176369541487565973)
            ·
              refine ⟨4917672945767322257229655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 104910356176369541487565973 4917672945767322257229655)
              ·
                refine ⟨7376509418650983385844483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4917672945767322257229655 7376509418650983385844483)
                ·
                  refine ⟨11064764127976475078766725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7376509418650983385844483 11064764127976475078766725)
                  ·
                    refine ⟨2074643273995589077268761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11064764127976475078766725 2074643273995589077268761)
                    ·
                      refine ⟨1555982455496691807951571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2074643273995589077268761 1555982455496691807951571)
                      ·
                        rfl

theorem cell23_3030265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 6, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 6, 1, 1, 4, 2].length) (baseStart_3030265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3030265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3030265 prefixEnd_3030265 := by exact prefixLift 3030265
  have htrace : WordTrace (prefixWord ++ tailWord_3030265) baseStart_3030265 baseEnd_3030265 := by
    simpa [prefixWord, tailWord_3030265, baseEnd_3030265] using wordTrace_append hprefix tailTrace_3030265
  have hstable : (prefixWord ++ tailWord_3030265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3030265).length < 2 ^ (prefixWord ++ tailWord_3030265).sum := by decide
  have hdescent : baseEnd_3030265 < baseStart_3030265 := by decide
  rcases family_descends (prefixWord ++ tailWord_3030265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3030271 : List Nat := [1, 1, 2, 2, 1, 5, 1, 1, 9]
def baseStart_3030271 : Nat := 118140960795 + 3030271 * 2 ^ 59
def prefixEnd_3030271 : Nat := 4983230072969 + 3 ^ 40 * 3030271 * 2
def baseEnd_3030271 : Nat := 172887281820068753830727

theorem tailTrace_3030271 : CollatzResearch.WordTrace tailWord_3030271 prefixEnd_3030271 172887281820068753830727 := by
  unfold tailWord_3030271
  simp only [CollatzResearch.WordTrace]
  refine ⟨110523063204853170929314667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73682042136568780619543111 110523063204853170929314667)
  ·
    refine ⟨165784594807279756393972001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110523063204853170929314667 165784594807279756393972001)
    ·
      refine ⟨124338446105459817295479001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 165784594807279756393972001 124338446105459817295479001)
      ·
        refine ⟨93253834579094862971609251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 124338446105459817295479001 93253834579094862971609251)
        ·
          refine ⟨139880751868642294457413877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93253834579094862971609251 139880751868642294457413877)
          ·
            refine ⟨13113820487685215105382551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 139880751868642294457413877 13113820487685215105382551)
            ·
              refine ⟨19670730731527822658073827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13113820487685215105382551 19670730731527822658073827)
              ·
                refine ⟨29506096097291733987110741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19670730731527822658073827 29506096097291733987110741)
                ·
                  refine ⟨172887281820068753830727, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 29506096097291733987110741 172887281820068753830727)
                  ·
                    rfl

theorem cell23_3030271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 1, 1, 9].length) (baseStart_3030271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3030271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3030271 prefixEnd_3030271 := by exact prefixLift 3030271
  have htrace : WordTrace (prefixWord ++ tailWord_3030271) baseStart_3030271 baseEnd_3030271 := by
    simpa [prefixWord, tailWord_3030271, baseEnd_3030271] using wordTrace_append hprefix tailTrace_3030271
  have hstable : (prefixWord ++ tailWord_3030271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3030271).length < 2 ^ (prefixWord ++ tailWord_3030271).sum := by decide
  have hdescent : baseEnd_3030271 < baseStart_3030271 := by decide
  rcases family_descends (prefixWord ++ tailWord_3030271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3030448 : List Nat := [2, 1, 1, 1, 2, 1, 1, 3, 5, 1, 5]
def baseStart_3030448 : Nat := 118140960795 + 3030448 * 2 ^ 59
def prefixEnd_3030448 : Nat := 4983230072969 + 3 ^ 40 * 3030448 * 2
def baseEnd_3030448 : Nat := 1556076422456464591963229

theorem tailTrace_3030448 : CollatzResearch.WordTrace tailWord_3030448 prefixEnd_3030448 1556076422456464591963229 := by
  unfold tailWord_3030448
  simp only [CollatzResearch.WordTrace]
  refine ⟨55264759462605965079253999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73686345950141286772338665 55264759462605965079253999)
  ·
    refine ⟨82897139193908947618880999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55264759462605965079253999 82897139193908947618880999)
    ·
      refine ⟨124345708790863421428321499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82897139193908947618880999 124345708790863421428321499)
      ·
        refine ⟨186518563186295132142482249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124345708790863421428321499 186518563186295132142482249)
        ·
          refine ⟨139888922389721349106861687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 186518563186295132142482249 139888922389721349106861687)
          ·
            refine ⟨209833383584582023660292531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 139888922389721349106861687 209833383584582023660292531)
            ·
              refine ⟨314750075376873035490438797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 209833383584582023660292531 314750075376873035490438797)
              ·
                refine ⟨118031278266327388308914549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 314750075376873035490438797 118031278266327388308914549)
                ·
                  refine ⟨11065432337468192653960739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 118031278266327388308914549 11065432337468192653960739)
                  ·
                    refine ⟨16598148506202288980941109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11065432337468192653960739 16598148506202288980941109)
                    ·
                      refine ⟨1556076422456464591963229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16598148506202288980941109 1556076422456464591963229)
                      ·
                        rfl

theorem cell23_3030448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 3, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 3, 5, 1, 5].length) (baseStart_3030448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3030448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3030448 prefixEnd_3030448 := by exact prefixLift 3030448
  have htrace : WordTrace (prefixWord ++ tailWord_3030448) baseStart_3030448 baseEnd_3030448 := by
    simpa [prefixWord, tailWord_3030448, baseEnd_3030448] using wordTrace_append hprefix tailTrace_3030448
  have hstable : (prefixWord ++ tailWord_3030448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3030448).length < 2 ^ (prefixWord ++ tailWord_3030448).sum := by decide
  have hdescent : baseEnd_3030448 < baseStart_3030448 := by decide
  rcases family_descends (prefixWord ++ tailWord_3030448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3030455 : List Nat := [1, 1, 3, 1, 3, 2, 2, 2, 4, 4]
def baseStart_3030455 : Nat := 118140960795 + 3030455 * 2 ^ 59
def prefixEnd_3030455 : Nat := 4983230072969 + 3 ^ 40 * 3030455 * 2
def baseEnd_3030455 : Nat := 518693338940348688191899

theorem tailTrace_3030455 : CollatzResearch.WordTrace tailWord_3030455 prefixEnd_3030455 518693338940348688191899 := by
  unfold tailWord_3030455
  simp only [CollatzResearch.WordTrace]
  refine ⟨110529774236186570354012819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73686516157457713569341879 110529774236186570354012819)
  ·
    refine ⟨165794661354279855531019229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110529774236186570354012819 165794661354279855531019229)
    ·
      refine ⟨62172998007854945824132211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 165794661354279855531019229 62172998007854945824132211)
      ·
        refine ⟨93259497011782418736198317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62172998007854945824132211 93259497011782418736198317)
        ·
          refine ⟨34972311379418407026074369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 93259497011782418736198317 34972311379418407026074369)
          ·
            refine ⟨26229233534563805269555777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34972311379418407026074369 26229233534563805269555777)
            ·
              refine ⟨19671925150922853952166833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26229233534563805269555777 19671925150922853952166833)
              ·
                refine ⟨14753943863192140464125125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19671925150922853952166833 14753943863192140464125125)
                ·
                  refine ⟨2766364474348526337023461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14753943863192140464125125 2766364474348526337023461)
                  ·
                    refine ⟨518693338940348688191899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2766364474348526337023461 518693338940348688191899)
                    ·
                      rfl

theorem cell23_3030455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 2, 2, 4, 4].length) (baseStart_3030455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3030455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3030455 prefixEnd_3030455 := by exact prefixLift 3030455
  have htrace : WordTrace (prefixWord ++ tailWord_3030455) baseStart_3030455 baseEnd_3030455 := by
    simpa [prefixWord, tailWord_3030455, baseEnd_3030455] using wordTrace_append hprefix tailTrace_3030455
  have hstable : (prefixWord ++ tailWord_3030455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3030455).length < 2 ^ (prefixWord ++ tailWord_3030455).sum := by decide
  have hdescent : baseEnd_3030455 < baseStart_3030455 := by decide
  rcases family_descends (prefixWord ++ tailWord_3030455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3030458 : List Nat := [3, 1, 1, 1, 2, 1, 1, 1, 5, 1, 6]
def baseStart_3030458 : Nat := 118140960795 + 3030458 * 2 ^ 59
def prefixEnd_3030458 : Nat := 4983230072969 + 3 ^ 40 * 3030458 * 2
def baseEnd_3030458 : Nat := 1556081557263009552838183

theorem tailTrace_3030458 : CollatzResearch.WordTrace tailWord_3030458 prefixEnd_3030458 1556081557263009552838183 := by
  unfold tailWord_3030458
  simp only [CollatzResearch.WordTrace]
  refine ⟨27632470913793925466593007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73686589103450467910914685 27632470913793925466593007)
  ·
    refine ⟨41448706370690888199889511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27632470913793925466593007 41448706370690888199889511)
    ·
      refine ⟨62173059556036332299834267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41448706370690888199889511 62173059556036332299834267)
      ·
        refine ⟨93259589334054498449751401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62173059556036332299834267 93259589334054498449751401)
        ·
          refine ⟨69944692000540873837313551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93259589334054498449751401 69944692000540873837313551)
          ·
            refine ⟨104917038000811310755970327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69944692000540873837313551 104917038000811310755970327)
            ·
              refine ⟨157375557001216966133955491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 104917038000811310755970327 157375557001216966133955491)
              ·
                refine ⟨236063335501825449200933237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 157375557001216966133955491 236063335501825449200933237)
                ·
                  refine ⟨22130937703296135862587491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 236063335501825449200933237 22130937703296135862587491)
                  ·
                    refine ⟨33196406554944203793881237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22130937703296135862587491 33196406554944203793881237)
                    ·
                      refine ⟨1556081557263009552838183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 33196406554944203793881237 1556081557263009552838183)
                      ·
                        rfl

theorem cell23_3030458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 1, 5, 1, 6].length) (baseStart_3030458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3030458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3030458 prefixEnd_3030458 := by exact prefixLift 3030458
  have htrace : WordTrace (prefixWord ++ tailWord_3030458) baseStart_3030458 baseEnd_3030458 := by
    simpa [prefixWord, tailWord_3030458, baseEnd_3030458] using wordTrace_append hprefix tailTrace_3030458
  have hstable : (prefixWord ++ tailWord_3030458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3030458).length < 2 ^ (prefixWord ++ tailWord_3030458).sum := by decide
  have hdescent : baseEnd_3030458 < baseStart_3030458 := by decide
  rcases family_descends (prefixWord ++ tailWord_3030458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3030489 : List Nat := [1, 2, 1, 2, 4, 3, 3, 1, 2, 4]
def baseStart_3030489 : Nat := 118140960795 + 3030489 * 2 ^ 59
def prefixEnd_3030489 : Nat := 4983230072969 + 3 ^ 40 * 3030489 * 2
def baseEnd_3030489 : Nat := 518699158387766310516847

theorem tailTrace_3030489 : CollatzResearch.WordTrace tailWord_3030489 prefixEnd_3030489 518699158387766310516847 := by
  unfold tailWord_3030489
  simp only [CollatzResearch.WordTrace]
  refine ⟨110531014318063394160750521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73687342878708929440500347 110531014318063394160750521)
  ·
    refine ⟨82898260738547545620562891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110531014318063394160750521 82898260738547545620562891)
    ·
      refine ⟨124347391107821318430844337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82898260738547545620562891 124347391107821318430844337)
      ·
        refine ⟨93260543330865988823133253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 124347391107821318430844337 93260543330865988823133253)
        ·
          refine ⟨17486351874537372904337485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 93260543330865988823133253 17486351874537372904337485)
          ·
            refine ⟨6557381952951514839126557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17486351874537372904337485 6557381952951514839126557)
            ·
              refine ⟨2459018232356818064672459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6557381952951514839126557 2459018232356818064672459)
              ·
                refine ⟨3688527348535227097008689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2459018232356818064672459 3688527348535227097008689)
                ·
                  refine ⟨2766395511401420322756517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3688527348535227097008689 2766395511401420322756517)
                  ·
                    refine ⟨518699158387766310516847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2766395511401420322756517 518699158387766310516847)
                    ·
                      rfl

theorem cell23_3030489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 3, 1, 2, 4].length) (baseStart_3030489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3030489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3030489 prefixEnd_3030489 := by exact prefixLift 3030489
  have htrace : WordTrace (prefixWord ++ tailWord_3030489) baseStart_3030489 baseEnd_3030489 := by
    simpa [prefixWord, tailWord_3030489, baseEnd_3030489] using wordTrace_append hprefix tailTrace_3030489
  have hstable : (prefixWord ++ tailWord_3030489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3030489).length < 2 ^ (prefixWord ++ tailWord_3030489).sum := by decide
  have hdescent : baseEnd_3030489 < baseStart_3030489 := by decide
  rcases family_descends (prefixWord ++ tailWord_3030489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3030499 : List Nat := [1, 1, 1, 6, 2, 2, 2, 2, 1, 2, 3]
def baseStart_3030499 : Nat := 118140960795 + 3030499 * 2 ^ 59
def prefixEnd_3030499 : Nat := 4983230072969 + 3 ^ 40 * 3030499 * 2
def baseEnd_3030499 : Nat := 1556102609969843892425495

theorem tailTrace_3030499 : CollatzResearch.WordTrace tailWord_3030499 prefixEnd_3030499 1556102609969843892425495 := by
  unfold tailWord_3030499
  simp only [CollatzResearch.WordTrace]
  refine ⟨110531379048027165868614551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73687586032018110579076367 110531379048027165868614551)
  ·
    refine ⟨165797068572040748802921827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110531379048027165868614551 165797068572040748802921827)
    ·
      refine ⟨248695602858061123204382741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165797068572040748802921827 248695602858061123204382741)
      ·
        refine ⟨11657606383971615150205441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 248695602858061123204382741 11657606383971615150205441)
        ·
          refine ⟨8743204787978711362654081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11657606383971615150205441 8743204787978711362654081)
          ·
            refine ⟨6557403590984033521990561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8743204787978711362654081 6557403590984033521990561)
            ·
              refine ⟨4918052693238025141492921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6557403590984033521990561 4918052693238025141492921)
              ·
                refine ⟨3688539519928518856119691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4918052693238025141492921 3688539519928518856119691)
                ·
                  refine ⟨5532809279892778284179537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3688539519928518856119691 5532809279892778284179537)
                  ·
                    refine ⟨4149606959919583713134653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5532809279892778284179537 4149606959919583713134653)
                    ·
                      refine ⟨1556102609969843892425495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4149606959919583713134653 1556102609969843892425495)
                      ·
                        rfl

theorem cell23_3030499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 2, 2, 1, 2, 3].length) (baseStart_3030499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3030499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3030499 prefixEnd_3030499 := by exact prefixLift 3030499
  have htrace : WordTrace (prefixWord ++ tailWord_3030499) baseStart_3030499 baseEnd_3030499 := by
    simpa [prefixWord, tailWord_3030499, baseEnd_3030499] using wordTrace_append hprefix tailTrace_3030499
  have hstable : (prefixWord ++ tailWord_3030499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3030499).length < 2 ^ (prefixWord ++ tailWord_3030499).sum := by decide
  have hdescent : baseEnd_3030499 < baseStart_3030499 := by decide
  rcases family_descends (prefixWord ++ tailWord_3030499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3030512 : List Nat := [2, 1, 1, 1, 3, 4, 1, 2, 4, 1, 3]
def baseStart_3030512 : Nat := 118140960795 + 3030512 * 2 ^ 59
def prefixEnd_3030512 : Nat := 4983230072969 + 3 ^ 40 * 3030512 * 2
def baseEnd_3030512 : Nat := 1556109285218352341562935

theorem tailTrace_3030512 : CollatzResearch.WordTrace tailWord_3030512 prefixEnd_3030512 1556109285218352341562935 := by
  unfold tailWord_3030512
  simp only [CollatzResearch.WordTrace]
  refine ⟨55265926598490034544418895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73687902131320046059225193 55265926598490034544418895)
  ·
    refine ⟨82898889897735051816628343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55265926598490034544418895 82898889897735051816628343)
    ·
      refine ⟨124348334846602577724942515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82898889897735051816628343 124348334846602577724942515)
      ·
        refine ⟨186522502269903866587413773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124348334846602577724942515 186522502269903866587413773)
        ·
          refine ⟨69945938351213949970280165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 186522502269903866587413773 69945938351213949970280165)
          ·
            refine ⟨13114863440852615619427531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 69945938351213949970280165 13114863440852615619427531)
            ·
              refine ⟨19672295161278923429141297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13114863440852615619427531 19672295161278923429141297)
              ·
                refine ⟨14754221370959192571855973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19672295161278923429141297 14754221370959192571855973)
                ·
                  refine ⟨2766416507054848607222995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14754221370959192571855973 2766416507054848607222995)
                  ·
                    refine ⟨4149624760582272910834493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2766416507054848607222995 4149624760582272910834493)
                    ·
                      refine ⟨1556109285218352341562935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4149624760582272910834493 1556109285218352341562935)
                      ·
                        rfl

theorem cell23_3030512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 1, 2, 4, 1, 3].length) (baseStart_3030512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3030512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3030512 prefixEnd_3030512 := by exact prefixLift 3030512
  have htrace : WordTrace (prefixWord ++ tailWord_3030512) baseStart_3030512 baseEnd_3030512 := by
    simpa [prefixWord, tailWord_3030512, baseEnd_3030512] using wordTrace_append hprefix tailTrace_3030512
  have hstable : (prefixWord ++ tailWord_3030512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3030512).length < 2 ^ (prefixWord ++ tailWord_3030512).sum := by decide
  have hdescent : baseEnd_3030512 < baseStart_3030512 := by decide
  rcases family_descends (prefixWord ++ tailWord_3030512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3030513 : List Nat := [1, 2, 2, 2, 3, 4, 1, 3, 1, 2, 2]
def baseStart_3030513 : Nat := 118140960795 + 3030513 * 2 ^ 59
def prefixEnd_3030513 : Nat := 4983230072969 + 3 ^ 40 * 3030513 * 2
def baseEnd_3030513 : Nat := 1556109798699006837650431

theorem tailTrace_3030513 : CollatzResearch.WordTrace tailWord_3030513 prefixEnd_3030513 1556109798699006837650431 := by
  unfold tailWord_3030513
  simp only [CollatzResearch.WordTrace]
  refine ⟨110531889669976446259624193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73687926446650964173082795 110531889669976446259624193)
  ·
    refine ⟨82898917252482334694718145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110531889669976446259624193 82898917252482334694718145)
    ·
      refine ⟨62174187939361751021038609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82898917252482334694718145 62174187939361751021038609)
      ·
        refine ⟨46630640954521313265778957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62174187939361751021038609 46630640954521313265778957)
        ·
          refine ⟨17486490357945492474667109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46630640954521313265778957 17486490357945492474667109)
          ·
            refine ⟨3278716942114779839000083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17486490357945492474667109 3278716942114779839000083)
            ·
              refine ⟨4918075413172169758500125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3278716942114779839000083 4918075413172169758500125)
              ·
                refine ⟨1844278279939563659437547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4918075413172169758500125 1844278279939563659437547)
                ·
                  refine ⟨2766417419909345489156321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1844278279939563659437547 2766417419909345489156321)
                  ·
                    refine ⟨2074813064932009116867241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2766417419909345489156321 2074813064932009116867241)
                    ·
                      refine ⟨1556109798699006837650431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2074813064932009116867241 1556109798699006837650431)
                      ·
                        rfl

theorem cell23_3030513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 4, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 4, 1, 3, 1, 2, 2].length) (baseStart_3030513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3030513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3030513 prefixEnd_3030513 := by exact prefixLift 3030513
  have htrace : WordTrace (prefixWord ++ tailWord_3030513) baseStart_3030513 baseEnd_3030513 := by
    simpa [prefixWord, tailWord_3030513, baseEnd_3030513] using wordTrace_append hprefix tailTrace_3030513
  have hstable : (prefixWord ++ tailWord_3030513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3030513).length < 2 ^ (prefixWord ++ tailWord_3030513).sum := by decide
  have hdescent : baseEnd_3030513 < baseStart_3030513 := by decide
  rcases family_descends (prefixWord ++ tailWord_3030513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3030565 : List Nat := [1, 3, 1, 2, 2, 1, 1, 2, 4, 2, 4]
def baseStart_3030565 : Nat := 118140960795 + 3030565 * 2 ^ 59
def prefixEnd_3030565 : Nat := 4983230072969 + 3 ^ 40 * 3030565 * 2
def baseEnd_3030565 : Nat := 1556136499693040634200191

theorem tailTrace_3030565 : CollatzResearch.WordTrace tailWord_3030565 prefixEnd_3030565 1556136499693040634200191 := by
  unfold tailWord_3030565
  simp only [CollatzResearch.WordTrace]
  refine ⟨110533786265788059140517149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73689190843858706093678099 110533786265788059140517149)
  ·
    refine ⟨41450169849670522177693931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 110533786265788059140517149 41450169849670522177693931)
    ·
      refine ⟨62175254774505783266540897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41450169849670522177693931 62175254774505783266540897)
      ·
        refine ⟨46631441080879337449905673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62175254774505783266540897 46631441080879337449905673)
        ·
          refine ⟨34973580810659503087429255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46631441080879337449905673 34973580810659503087429255)
          ·
            refine ⟨52460371215989254631143883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34973580810659503087429255 52460371215989254631143883)
            ·
              refine ⟨78690556823983881946715825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52460371215989254631143883 78690556823983881946715825)
              ·
                refine ⟨59017917617987911460036869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 78690556823983881946715825 59017917617987911460036869)
                ·
                  refine ⟨11065859553372733398756913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 59017917617987911460036869 11065859553372733398756913)
                  ·
                    refine ⟨8299394665029550049067685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11065859553372733398756913 8299394665029550049067685)
                    ·
                      refine ⟨1556136499693040634200191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8299394665029550049067685 1556136499693040634200191)
                      ·
                        rfl

theorem cell23_3030565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 2, 4, 2, 4].length) (baseStart_3030565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3030565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3030565 prefixEnd_3030565 := by exact prefixLift 3030565
  have htrace : WordTrace (prefixWord ++ tailWord_3030565) baseStart_3030565 baseEnd_3030565 := by
    simpa [prefixWord, tailWord_3030565, baseEnd_3030565] using wordTrace_append hprefix tailTrace_3030565
  have hstable : (prefixWord ++ tailWord_3030565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3030565).length < 2 ^ (prefixWord ++ tailWord_3030565).sum := by decide
  have hdescent : baseEnd_3030565 < baseStart_3030565 := by decide
  rcases family_descends (prefixWord ++ tailWord_3030565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3030586 : List Nat := [3, 1, 1, 1, 3, 2, 4, 2, 2, 2, 2]
def baseStart_3030586 : Nat := 118140960795 + 3030586 * 2 ^ 59
def prefixEnd_3030586 : Nat := 4983230072969 + 3 ^ 40 * 3030586 * 2
def baseEnd_3030586 : Nat := 1556147282786785052037595

theorem tailTrace_3030586 : CollatzResearch.WordTrace tailWord_3030586 prefixEnd_3030586 1556147282786785052037595 := by
  unfold tailWord_3030586
  simp only [CollatzResearch.WordTrace]
  refine ⟨27633638049677994931757903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73689701465807986484687741 27633638049677994931757903)
  ·
    refine ⟨41450457074516992397636855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27633638049677994931757903 41450457074516992397636855)
    ·
      refine ⟨62175685611775488596455283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41450457074516992397636855 62175685611775488596455283)
      ·
        refine ⟨93263528417663232894682925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62175685611775488596455283 93263528417663232894682925)
        ·
          refine ⟨34973823156623712335506097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 93263528417663232894682925 34973823156623712335506097)
          ·
            refine ⟨26230367367467784251629573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34973823156623712335506097 26230367367467784251629573)
            ·
              refine ⟨4918193881400209547180545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26230367367467784251629573 4918193881400209547180545)
              ·
                refine ⟨3688645411050157160385409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4918193881400209547180545 3688645411050157160385409)
                ·
                  refine ⟨2766484058287617870289057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3688645411050157160385409 2766484058287617870289057)
                  ·
                    refine ⟨2074863043715713402716793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2766484058287617870289057 2074863043715713402716793)
                    ·
                      refine ⟨1556147282786785052037595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2074863043715713402716793 1556147282786785052037595)
                      ·
                        rfl

theorem cell23_3030586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 4, 2, 2, 2, 2].length) (baseStart_3030586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3030586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3030586 prefixEnd_3030586 := by exact prefixLift 3030586
  have htrace : WordTrace (prefixWord ++ tailWord_3030586) baseStart_3030586 baseEnd_3030586 := by
    simpa [prefixWord, tailWord_3030586, baseEnd_3030586] using wordTrace_append hprefix tailTrace_3030586
  have hstable : (prefixWord ++ tailWord_3030586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3030586).length < 2 ^ (prefixWord ++ tailWord_3030586).sum := by decide
  have hdescent : baseEnd_3030586 < baseStart_3030586 := by decide
  rcases family_descends (prefixWord ++ tailWord_3030586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3030602 : List Nat := [3, 1, 2, 1, 1, 3, 3, 1, 2, 3, 3]
def baseStart_3030602 : Nat := 118140960795 + 3030602 * 2 ^ 59
def prefixEnd_3030602 : Nat := 4983230072969 + 3 ^ 40 * 3030602 * 2
def baseEnd_3030602 : Nat := 1556155498477256989437521

theorem tailTrace_3030602 : CollatzResearch.WordTrace tailWord_3030602 prefixEnd_3030602 1556155498477256989437521 := by
  unfold tailWord_3030602
  simp only [CollatzResearch.WordTrace]
  refine ⟨27633783941663503614903515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73690090511102676306409373 27633783941663503614903515)
  ·
    refine ⟨41450675912495255422355273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27633783941663503614903515 41450675912495255422355273)
    ·
      refine ⟨31088006934371441566766455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41450675912495255422355273 31088006934371441566766455)
      ·
        refine ⟨46632010401557162350149683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31088006934371441566766455 46632010401557162350149683)
        ·
          refine ⟨69948015602335743525224525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46632010401557162350149683 69948015602335743525224525)
          ·
            refine ⟨26230505850875903821959197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 69948015602335743525224525 26230505850875903821959197)
            ·
              refine ⟨9836439694078463933234699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26230505850875903821959197 9836439694078463933234699)
              ·
                refine ⟨14754659541117695899852049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9836439694078463933234699 14754659541117695899852049)
                ·
                  refine ⟨11065994655838271924889037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14754659541117695899852049 11065994655838271924889037)
                  ·
                    refine ⟨4149747995939351971833389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11065994655838271924889037 4149747995939351971833389)
                    ·
                      refine ⟨1556155498477256989437521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4149747995939351971833389 1556155498477256989437521)
                      ·
                        rfl

theorem cell23_3030602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 3, 1, 2, 3, 3].length) (baseStart_3030602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3030602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3030602 prefixEnd_3030602 := by exact prefixLift 3030602
  have htrace : WordTrace (prefixWord ++ tailWord_3030602) baseStart_3030602 baseEnd_3030602 := by
    simpa [prefixWord, tailWord_3030602, baseEnd_3030602] using wordTrace_append hprefix tailTrace_3030602
  have hstable : (prefixWord ++ tailWord_3030602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3030602).length < 2 ^ (prefixWord ++ tailWord_3030602).sum := by decide
  have hdescent : baseEnd_3030602 < baseStart_3030602 := by decide
  rcases family_descends (prefixWord ++ tailWord_3030602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3030716 : List Nat := [2, 2, 2, 3, 1, 4, 2, 1, 6]
def baseStart_3030716 : Nat := 118140960795 + 3030716 * 2 ^ 59
def prefixEnd_3030716 : Nat := 4983230072969 + 3 ^ 40 * 3030716 * 2
def baseEnd_3030716 : Nat := 172912670585763282601333

theorem tailTrace_3030716 : CollatzResearch.WordTrace tailWord_3030716 prefixEnd_3030716 172912670585763282601333 := by
  unfold tailWord_3030716
  simp only [CollatzResearch.WordTrace]
  refine ⟨55269646844120505964632001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73692862458827341286176001 55269646844120505964632001)
  ·
    refine ⟨41452235133090379473474001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55269646844120505964632001 41452235133090379473474001)
    ·
      refine ⟨31089176349817784605105501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41452235133090379473474001 31089176349817784605105501)
      ·
        refine ⟨11658441131181669226914563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31089176349817784605105501 11658441131181669226914563)
        ·
          refine ⟨17487661696772503840371845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11658441131181669226914563 17487661696772503840371845)
          ·
            refine ⟨3278936568144844470069721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17487661696772503840371845 3278936568144844470069721)
            ·
              refine ⟨2459202426108633352552291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3278936568144844470069721 2459202426108633352552291)
              ·
                refine ⟨3688803639162950028828437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2459202426108633352552291 3688803639162950028828437)
                ·
                  refine ⟨172912670585763282601333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3688803639162950028828437 172912670585763282601333)
                  ·
                    rfl

theorem cell23_3030716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 4, 2, 1, 6].length) (baseStart_3030716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3030716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3030716 prefixEnd_3030716 := by exact prefixLift 3030716
  have htrace : WordTrace (prefixWord ++ tailWord_3030716) baseStart_3030716 baseEnd_3030716 := by
    simpa [prefixWord, tailWord_3030716, baseEnd_3030716] using wordTrace_append hprefix tailTrace_3030716
  have hstable : (prefixWord ++ tailWord_3030716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3030716).length < 2 ^ (prefixWord ++ tailWord_3030716).sum := by decide
  have hdescent : baseEnd_3030716 < baseStart_3030716 := by decide
  rcases family_descends (prefixWord ++ tailWord_3030716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3030719 : List Nat := [1, 1, 2, 2, 2, 3, 1, 2, 4, 3, 2]
def baseStart_3030719 : Nat := 118140960795 + 3030719 * 2 ^ 59
def prefixEnd_3030719 : Nat := 4983230072969 + 3 ^ 40 * 3030719 * 2
def baseEnd_3030719 : Nat := 1556215575713833031674483

theorem tailTrace_3030719 : CollatzResearch.WordTrace tailWord_3030719 prefixEnd_3030719 1556215575713833031674483 := by
  unfold tailWord_3030719
  simp only [CollatzResearch.WordTrace]
  refine ⟨110539403107230143441623211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73692935404820095627748807 110539403107230143441623211)
  ·
    refine ⟨165809104660845215162434817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110539403107230143441623211 165809104660845215162434817)
    ·
      refine ⟨124356828495633911371826113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 165809104660845215162434817 124356828495633911371826113)
      ·
        refine ⟨93267621371725433528869585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 124356828495633911371826113 93267621371725433528869585)
        ·
          refine ⟨69950716028794075146652189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93267621371725433528869585 69950716028794075146652189)
          ·
            refine ⟨26231518510797778179994571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 69950716028794075146652189 26231518510797778179994571)
            ·
              refine ⟨39347277766196667269991857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26231518510797778179994571 39347277766196667269991857)
              ·
                refine ⟨29510458324647500452493893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39347277766196667269991857 29510458324647500452493893)
                ·
                  refine ⟨5533210935871406334842605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29510458324647500452493893 5533210935871406334842605)
                  ·
                    refine ⟨2074954100951777375565977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5533210935871406334842605 2074954100951777375565977)
                    ·
                      refine ⟨1556215575713833031674483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2074954100951777375565977 1556215575713833031674483)
                      ·
                        rfl

theorem cell23_3030719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 2, 4, 3, 2].length) (baseStart_3030719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3030719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3030719 prefixEnd_3030719 := by exact prefixLift 3030719
  have htrace : WordTrace (prefixWord ++ tailWord_3030719) baseStart_3030719 baseEnd_3030719 := by
    simpa [prefixWord, tailWord_3030719, baseEnd_3030719] using wordTrace_append hprefix tailTrace_3030719
  have hstable : (prefixWord ++ tailWord_3030719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3030719).length < 2 ^ (prefixWord ++ tailWord_3030719).sum := by decide
  have hdescent : baseEnd_3030719 < baseStart_3030719 := by decide
  rcases family_descends (prefixWord ++ tailWord_3030719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3030746 : List Nat := [3, 1, 1, 2, 2, 4, 3, 1, 1, 5]
def baseStart_3030746 : Nat := 118140960795 + 3030746 * 2 ^ 59
def prefixEnd_3030746 : Nat := 4983230072969 + 3 ^ 40 * 3030746 * 2
def baseEnd_3030746 : Nat := 518743146563834808678953

theorem tailTrace_3030746 : CollatzResearch.WordTrace tailWord_3030746 prefixEnd_3030746 518743146563834808678953 := by
  unfold tailWord_3030746
  simp only [CollatzResearch.WordTrace]
  refine ⟨27635096969533081763214023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73693591918754884701904061 27635096969533081763214023)
  ·
    refine ⟨41452645454299622644821035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27635096969533081763214023 41452645454299622644821035)
    ·
      refine ⟨62178968181449433967231553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41452645454299622644821035 62178968181449433967231553)
      ·
        refine ⟨46634226136087075475423665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62178968181449433967231553 46634226136087075475423665)
        ·
          refine ⟨34975669602065306606567749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46634226136087075475423665 34975669602065306606567749)
          ·
            refine ⟨6557938050387244988731453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34975669602065306606567749 6557938050387244988731453)
            ·
              refine ⟨2459226768895216870774295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6557938050387244988731453 2459226768895216870774295)
              ·
                refine ⟨3688840153342825306161443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2459226768895216870774295 3688840153342825306161443)
                ·
                  refine ⟨5533260230014237959242165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3688840153342825306161443 5533260230014237959242165)
                  ·
                    refine ⟨518743146563834808678953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5533260230014237959242165 518743146563834808678953)
                    ·
                      rfl

theorem cell23_3030746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 3, 1, 1, 5].length) (baseStart_3030746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3030746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3030746 prefixEnd_3030746 := by exact prefixLift 3030746
  have htrace : WordTrace (prefixWord ++ tailWord_3030746) baseStart_3030746 baseEnd_3030746 := by
    simpa [prefixWord, tailWord_3030746, baseEnd_3030746] using wordTrace_append hprefix tailTrace_3030746
  have hstable : (prefixWord ++ tailWord_3030746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3030746).length < 2 ^ (prefixWord ++ tailWord_3030746).sum := by decide
  have hdescent : baseEnd_3030746 < baseStart_3030746 := by decide
  rcases family_descends (prefixWord ++ tailWord_3030746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3030760 : List Nat := [2, 1, 4, 1, 3, 1, 4, 2, 1, 1, 3]
def baseStart_3030760 : Nat := 118140960795 + 3030760 * 2 ^ 59
def prefixEnd_3030760 : Nat := 4983230072969 + 3 ^ 40 * 3030760 * 2
def baseEnd_3030760 : Nat := 1556236628420667371261795

theorem tailTrace_3030760 : CollatzResearch.WordTrace tailWord_3030760 prefixEnd_3030760 1556236628420667371261795 := by
  unfold tailWord_3030760
  simp only [CollatzResearch.WordTrace]
  refine ⟨55270449250040803721932867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73693932333387738295910489 55270449250040803721932867)
  ·
    refine ⟨82905673875061205582899301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55270449250040803721932867 82905673875061205582899301)
    ·
      refine ⟨15544813851573976046793619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 82905673875061205582899301 15544813851573976046793619)
      ·
        refine ⟨23317220777360964070190429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15544813851573976046793619 23317220777360964070190429)
        ·
          refine ⟨8743957791510361526321411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23317220777360964070190429 8743957791510361526321411)
          ·
            refine ⟨13115936687265542289482117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8743957791510361526321411 13115936687265542289482117)
            ·
              refine ⟨2459238128862289179277897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13115936687265542289482117 2459238128862289179277897)
              ·
                refine ⟨1844428596646716884458423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2459238128862289179277897 1844428596646716884458423)
                ·
                  refine ⟨2766642894970075326687635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1844428596646716884458423 2766642894970075326687635)
                  ·
                    refine ⟨4149964342455112990031453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2766642894970075326687635 4149964342455112990031453)
                    ·
                      refine ⟨1556236628420667371261795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4149964342455112990031453 1556236628420667371261795)
                      ·
                        rfl

theorem cell23_3030760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 4, 2, 1, 1, 3].length) (baseStart_3030760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3030760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3030760 prefixEnd_3030760 := by exact prefixLift 3030760
  have htrace : WordTrace (prefixWord ++ tailWord_3030760) baseStart_3030760 baseEnd_3030760 := by
    simpa [prefixWord, tailWord_3030760, baseEnd_3030760] using wordTrace_append hprefix tailTrace_3030760
  have hstable : (prefixWord ++ tailWord_3030760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3030760).length < 2 ^ (prefixWord ++ tailWord_3030760).sum := by decide
  have hdescent : baseEnd_3030760 < baseStart_3030760 := by decide
  rcases family_descends (prefixWord ++ tailWord_3030760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3030762 : List Nat := [3, 1, 3, 1, 1, 1, 2, 1, 3, 1, 6]
def baseStart_3030762 : Nat := 118140960795 + 3030762 * 2 ^ 59
def prefixEnd_3030762 : Nat := 4983230072969 + 3 ^ 40 * 3030762 * 2
def baseEnd_3030762 : Nat := 1556237655381976363436785

theorem tailTrace_3030762 : CollatzResearch.WordTrace tailWord_3030762 prefixEnd_3030762 1556237655381976363436785 := by
  unfold tailWord_3030762
  simp only [CollatzResearch.WordTrace]
  refine ⟨27635242861518590446359635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73693980964049574523625693 27635242861518590446359635)
  ·
    refine ⟨41452864292277885669539453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27635242861518590446359635 41452864292277885669539453)
    ·
      refine ⟨15544824109604207126077295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41452864292277885669539453 15544824109604207126077295)
      ·
        refine ⟨23317236164406310689115943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15544824109604207126077295 23317236164406310689115943)
        ·
          refine ⟨34975854246609466033673915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23317236164406310689115943 34975854246609466033673915)
          ·
            refine ⟨52463781369914199050510873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34975854246609466033673915 52463781369914199050510873)
            ·
              refine ⟨39347836027435649287883155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52463781369914199050510873 39347836027435649287883155)
              ·
                refine ⟨59021754041153473931824733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39347836027435649287883155 59021754041153473931824733)
                ·
                  refine ⟨22133157765432552724434275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 59021754041153473931824733 22133157765432552724434275)
                  ·
                    refine ⟨33199736648148829086651413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22133157765432552724434275 33199736648148829086651413)
                    ·
                      refine ⟨1556237655381976363436785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 33199736648148829086651413 1556237655381976363436785)
                      ·
                        rfl

theorem cell23_3030762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 1, 3, 1, 6].length) (baseStart_3030762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3030762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3030762 prefixEnd_3030762 := by exact prefixLift 3030762
  have htrace : WordTrace (prefixWord ++ tailWord_3030762) baseStart_3030762 baseEnd_3030762 := by
    simpa [prefixWord, tailWord_3030762, baseEnd_3030762] using wordTrace_append hprefix tailTrace_3030762
  have hstable : (prefixWord ++ tailWord_3030762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3030762).length < 2 ^ (prefixWord ++ tailWord_3030762).sum := by decide
  have hdescent : baseEnd_3030762 < baseStart_3030762 := by decide
  rcases family_descends (prefixWord ++ tailWord_3030762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3030769 : List Nat := [1, 2, 2, 2, 2, 3, 1, 2, 3, 2, 3]
def baseStart_3030769 : Nat := 118140960795 + 3030769 * 2 ^ 59
def prefixEnd_3030769 : Nat := 4983230072969 + 3 ^ 40 * 3030769 * 2
def baseEnd_3030769 : Nat := 1556241249746557836049253

theorem tailTrace_3030769 : CollatzResearch.WordTrace tailWord_3030769 prefixEnd_3030769 1556241249746557836049253 := by
  unfold tailWord_3030769
  simp only [CollatzResearch.WordTrace]
  refine ⟨110541226757049001980943361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73694151171366001320628907 110541226757049001980943361)
  ·
    refine ⟨82905920067786751485707521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110541226757049001980943361 82905920067786751485707521)
    ·
      refine ⟨62179440050840063614280641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82905920067786751485707521 62179440050840063614280641)
      ·
        refine ⟨46634580038130047710710481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62179440050840063614280641 46634580038130047710710481)
        ·
          refine ⟨34975935028597535783032861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46634580038130047710710481 34975935028597535783032861)
          ·
            refine ⟨13115975635724075918637323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34975935028597535783032861 13115975635724075918637323)
            ·
              refine ⟨19673963453586113877955985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13115975635724075918637323 19673963453586113877955985)
              ·
                refine ⟨14755472590189585408466989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19673963453586113877955985 14755472590189585408466989)
                ·
                  refine ⟨5533302221321094528175121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14755472590189585408466989 5533302221321094528175121)
                  ·
                    refine ⟨4149976665990820896131341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5533302221321094528175121 4149976665990820896131341)
                    ·
                      refine ⟨1556241249746557836049253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4149976665990820896131341 1556241249746557836049253)
                      ·
                        rfl

theorem cell23_3030769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 1, 2, 3, 2, 3].length) (baseStart_3030769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3030769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3030769 prefixEnd_3030769 := by exact prefixLift 3030769
  have htrace : WordTrace (prefixWord ++ tailWord_3030769) baseStart_3030769 baseEnd_3030769 := by
    simpa [prefixWord, tailWord_3030769, baseEnd_3030769] using wordTrace_append hprefix tailTrace_3030769
  have hstable : (prefixWord ++ tailWord_3030769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3030769).length < 2 ^ (prefixWord ++ tailWord_3030769).sum := by decide
  have hdescent : baseEnd_3030769 < baseStart_3030769 := by decide
  rcases family_descends (prefixWord ++ tailWord_3030769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3030786 : List Nat := [3, 4, 1, 1, 1, 1, 1, 3, 3, 2, 3]
def baseStart_3030786 : Nat := 118140960795 + 3030786 * 2 ^ 59
def prefixEnd_3030786 : Nat := 4983230072969 + 3 ^ 40 * 3030786 * 2
def baseEnd_3030786 : Nat := 1556249978917684269536675

theorem tailTrace_3030786 : CollatzResearch.WordTrace tailWord_3030786 prefixEnd_3030786 1556249978917684269536675 := by
  unfold tailWord_3030786
  simp only [CollatzResearch.WordTrace]
  refine ⟨27635461699496853471078053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73694564531991609256208141 27635461699496853471078053)
  ·
    refine ⟨5181649068655660025827135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27635461699496853471078053 5181649068655660025827135)
    ·
      refine ⟨7772473602983490038740703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5181649068655660025827135 7772473602983490038740703)
      ·
        refine ⟨11658710404475235058111055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7772473602983490038740703 11658710404475235058111055)
        ·
          refine ⟨17488065606712852587166583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11658710404475235058111055 17488065606712852587166583)
          ·
            refine ⟨26232098410069278880749875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17488065606712852587166583 26232098410069278880749875)
            ·
              refine ⟨39348147615103918321124813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26232098410069278880749875 39348147615103918321124813)
              ·
                refine ⟨14755555355663969370421805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39348147615103918321124813 14755555355663969370421805)
                ·
                  refine ⟨5533333258373988513908177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14755555355663969370421805 5533333258373988513908177)
                  ·
                    refine ⟨4149999943780491385431133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5533333258373988513908177 4149999943780491385431133)
                    ·
                      refine ⟨1556249978917684269536675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4149999943780491385431133 1556249978917684269536675)
                      ·
                        rfl

theorem cell23_3030786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 3, 3, 2, 3].length) (baseStart_3030786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3030786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3030786 prefixEnd_3030786 := by exact prefixLift 3030786
  have htrace : WordTrace (prefixWord ++ tailWord_3030786) baseStart_3030786 baseEnd_3030786 := by
    simpa [prefixWord, tailWord_3030786, baseEnd_3030786] using wordTrace_append hprefix tailTrace_3030786
  have hstable : (prefixWord ++ tailWord_3030786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3030786).length < 2 ^ (prefixWord ++ tailWord_3030786).sum := by decide
  have hdescent : baseEnd_3030786 < baseStart_3030786 := by decide
  rcases family_descends (prefixWord ++ tailWord_3030786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3030797 : List Nat := [1, 7, 2, 1, 1, 1, 1, 3, 1, 5]
def baseStart_3030797 : Nat := 118140960795 + 3030797 * 2 ^ 59
def prefixEnd_3030797 : Nat := 4983230072969 + 3 ^ 40 * 3030797 * 2
def baseEnd_3030797 : Nat := 518751875734961242166375

theorem tailTrace_3030797 : CollatzResearch.WordTrace tailWord_3030797 prefixEnd_3030797 518751875734961242166375 := by
  unfold tailWord_3030797
  simp only [CollatzResearch.WordTrace]
  refine ⟨110542248000947562762962645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73694832000631708508641763 110542248000947562762962645)
  ·
    refine ⟨2590833937522208502256937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 110542248000947562762962645 2590833937522208502256937)
    ·
      refine ⟨1943125453141656376692703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2590833937522208502256937 1943125453141656376692703)
      ·
        refine ⟨2914688179712484565039055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1943125453141656376692703 2914688179712484565039055)
        ·
          refine ⟨4372032269568726847558583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2914688179712484565039055 4372032269568726847558583)
          ·
            refine ⟨6558048404353090271337875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4372032269568726847558583 6558048404353090271337875)
            ·
              refine ⟨9837072606529635407006813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6558048404353090271337875 9837072606529635407006813)
              ·
                refine ⟨3688902227448613277627555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9837072606529635407006813 3688902227448613277627555)
                ·
                  refine ⟨5533353341172919916441333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3688902227448613277627555 5533353341172919916441333)
                  ·
                    refine ⟨518751875734961242166375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5533353341172919916441333 518751875734961242166375)
                    ·
                      rfl

theorem cell23_3030797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 1, 3, 1, 5].length) (baseStart_3030797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3030797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3030797 prefixEnd_3030797 := by exact prefixLift 3030797
  have htrace : WordTrace (prefixWord ++ tailWord_3030797) baseStart_3030797 baseEnd_3030797 := by
    simpa [prefixWord, tailWord_3030797, baseEnd_3030797] using wordTrace_append hprefix tailTrace_3030797
  have hstable : (prefixWord ++ tailWord_3030797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3030797).length < 2 ^ (prefixWord ++ tailWord_3030797).sum := by decide
  have hdescent : baseEnd_3030797 < baseStart_3030797 := by decide
  rcases family_descends (prefixWord ++ tailWord_3030797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3030816 : List Nat := [2, 1, 1, 5, 1, 1, 3, 1, 4, 1, 3]
def baseStart_3030816 : Nat := 118140960795 + 3030816 * 2 ^ 59
def prefixEnd_3030816 : Nat := 4983230072969 + 3 ^ 40 * 3030816 * 2
def baseEnd_3030816 : Nat := 1556265383337319152161537

theorem tailTrace_3030816 : CollatzResearch.WordTrace tailWord_3030816 prefixEnd_3030816 1556265383337319152161537 := by
  unfold tailWord_3030816
  simp only [CollatzResearch.WordTrace]
  refine ⟨55271470493939364503952151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73695293991919152671936201 55271470493939364503952151)
  ·
    refine ⟨82907205740909046755928227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55271470493939364503952151 82907205740909046755928227)
    ·
      refine ⟨124360808611363570133892341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82907205740909046755928227 124360808611363570133892341)
      ·
        refine ⟨11658825807315334700052407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 124360808611363570133892341 11658825807315334700052407)
        ·
          refine ⟨17488238710973002050078611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11658825807315334700052407 17488238710973002050078611)
          ·
            refine ⟨26232358066459503075117917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17488238710973002050078611 26232358066459503075117917)
            ·
              refine ⟨9837134274922313653169219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26232358066459503075117917 9837134274922313653169219)
              ·
                refine ⟨14755701412383470479753829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9837134274922313653169219 14755701412383470479753829)
                ·
                  refine ⟨2766694014821900714953843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14755701412383470479753829 2766694014821900714953843)
                  ·
                    refine ⟨4150041022232851072430765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2766694014821900714953843 4150041022232851072430765)
                    ·
                      refine ⟨1556265383337319152161537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4150041022232851072430765 1556265383337319152161537)
                      ·
                        rfl

theorem cell23_3030816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 3, 1, 4, 1, 3].length) (baseStart_3030816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3030816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3030816 prefixEnd_3030816 := by exact prefixLift 3030816
  have htrace : WordTrace (prefixWord ++ tailWord_3030816) baseStart_3030816 baseEnd_3030816 := by
    simpa [prefixWord, tailWord_3030816, baseEnd_3030816] using wordTrace_append hprefix tailTrace_3030816
  have hstable : (prefixWord ++ tailWord_3030816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3030816).length < 2 ^ (prefixWord ++ tailWord_3030816).sum := by decide
  have hdescent : baseEnd_3030816 < baseStart_3030816 := by decide
  rcases family_descends (prefixWord ++ tailWord_3030816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3030830 : List Nat := [4, 1, 3, 2, 3, 1, 1, 1, 1, 2, 4]
def baseStart_3030830 : Nat := 118140960795 + 3030830 * 2 ^ 59
def prefixEnd_3030830 : Nat := 4983230072969 + 3 ^ 40 * 3030830 * 2
def baseEnd_3030830 : Nat := 1556272572066482097386473

theorem tailTrace_3030830 : CollatzResearch.WordTrace tailWord_3030830 prefixEnd_3030830 1556272572066482097386473 := by
  unfold tailWord_3030830
  simp only [CollatzResearch.WordTrace]
  refine ⟨13817931451228501174864243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 73695634406552006265942629 13817931451228501174864243)
  ·
    refine ⟨20726897176842751762296365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13817931451228501174864243 20726897176842751762296365)
    ·
      refine ⟨7772586441316031910861137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20726897176842751762296365 7772586441316031910861137)
      ·
        refine ⟨5829439830987023933145853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7772586441316031910861137 5829439830987023933145853)
        ·
          refine ⟨2186039936620133974929695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5829439830987023933145853 2186039936620133974929695)
          ·
            refine ⟨3279059904930200962394543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2186039936620133974929695 3279059904930200962394543)
            ·
              refine ⟨4918589857395301443591815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3279059904930200962394543 4918589857395301443591815)
              ·
                refine ⟨7377884786092952165387723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4918589857395301443591815 7377884786092952165387723)
                ·
                  refine ⟨11066827179139428248081585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7377884786092952165387723 11066827179139428248081585)
                  ·
                    refine ⟨8300120384354571186061189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11066827179139428248081585 8300120384354571186061189)
                    ·
                      refine ⟨1556272572066482097386473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8300120384354571186061189 1556272572066482097386473)
                      ·
                        rfl

theorem cell23_3030830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 3, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 3, 1, 1, 1, 1, 2, 4].length) (baseStart_3030830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3030830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3030830 prefixEnd_3030830 := by exact prefixLift 3030830
  have htrace : WordTrace (prefixWord ++ tailWord_3030830) baseStart_3030830 baseEnd_3030830 := by
    simpa [prefixWord, tailWord_3030830, baseEnd_3030830] using wordTrace_append hprefix tailTrace_3030830
  have hstable : (prefixWord ++ tailWord_3030830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3030830).length < 2 ^ (prefixWord ++ tailWord_3030830).sum := by decide
  have hdescent : baseEnd_3030830 < baseStart_3030830 := by decide
  rcases family_descends (prefixWord ++ tailWord_3030830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3030873 : List Nat := [1, 2, 1, 2, 2, 3, 2, 4, 2, 2, 2]
def baseStart_3030873 : Nat := 118140960795 + 3030873 * 2 ^ 59
def prefixEnd_3030873 : Nat := 4983230072969 + 3 ^ 40 * 3030873 * 2
def baseEnd_3030873 : Nat := 1556294651734625429148775

theorem tailTrace_3030873 : CollatzResearch.WordTrace tailWord_3030873 prefixEnd_3030873 1556294651734625429148775 := by
  unfold tailWord_3030873
  simp only [CollatzResearch.WordTrace]
  refine ⟨110545019948672227742729273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73696679965781485161819515 110545019948672227742729273)
  ·
    refine ⟨82908764961504170807046955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110545019948672227742729273 82908764961504170807046955)
    ·
      refine ⟨124363147442256256210570433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82908764961504170807046955 124363147442256256210570433)
      ·
        refine ⟨93272360581692192157927825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 124363147442256256210570433 93272360581692192157927825)
        ·
          refine ⟨69954270436269144118445869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93272360581692192157927825 69954270436269144118445869)
          ·
            refine ⟨26232851413600929044417201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 69954270436269144118445869 26232851413600929044417201)
            ·
              refine ⟨19674638560200696783312901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26232851413600929044417201 19674638560200696783312901)
              ·
                refine ⟨3688994730037630646871169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19674638560200696783312901 3688994730037630646871169)
                ·
                  refine ⟨2766746047528222985153377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3688994730037630646871169 2766746047528222985153377)
                  ·
                    refine ⟨2075059535646167238865033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2766746047528222985153377 2075059535646167238865033)
                    ·
                      refine ⟨1556294651734625429148775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2075059535646167238865033 1556294651734625429148775)
                      ·
                        rfl

theorem cell23_3030873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 2, 4, 2, 2, 2].length) (baseStart_3030873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3030873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3030873 prefixEnd_3030873 := by exact prefixLift 3030873
  have htrace : WordTrace (prefixWord ++ tailWord_3030873) baseStart_3030873 baseEnd_3030873 := by
    simpa [prefixWord, tailWord_3030873, baseEnd_3030873] using wordTrace_append hprefix tailTrace_3030873
  have hstable : (prefixWord ++ tailWord_3030873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3030873).length < 2 ^ (prefixWord ++ tailWord_3030873).sum := by decide
  have hdescent : baseEnd_3030873 < baseStart_3030873 := by decide
  rcases family_descends (prefixWord ++ tailWord_3030873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3030879 : List Nat := [1, 1, 2, 3, 1, 4, 3, 1, 7]
def baseStart_3030879 : Nat := 118140960795 + 3030879 * 2 ^ 59
def prefixEnd_3030879 : Nat := 4983230072969 + 3 ^ 40 * 3030879 * 2
def baseEnd_3030879 : Nat := 172921970290950267297083

theorem tailTrace_3030879 : CollatzResearch.WordTrace tailWord_3030879 prefixEnd_3030879 172921970290950267297083 := by
  unfold tailWord_3030879
  simp only [CollatzResearch.WordTrace]
  refine ⟨110545238786650490767447691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73696825857766993844965127 110545238786650490767447691)
  ·
    refine ⟨165817858179975736151171537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110545238786650490767447691 165817858179975736151171537)
    ·
      refine ⟨124363393634981802113378653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 165817858179975736151171537 124363393634981802113378653)
      ·
        refine ⟨46636272613118175792516995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 124363393634981802113378653 46636272613118175792516995)
        ·
          refine ⟨69954408919677263688775493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46636272613118175792516995 69954408919677263688775493)
          ·
            refine ⟨13116451672439486941645405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 69954408919677263688775493 13116451672439486941645405)
            ·
              refine ⟨4918669377164807603117027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13116451672439486941645405 4918669377164807603117027)
              ·
                refine ⟨7378004065747211404675541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4918669377164807603117027 7378004065747211404675541)
                ·
                  refine ⟨172921970290950267297083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7378004065747211404675541 172921970290950267297083)
                  ·
                    rfl

theorem cell23_3030879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 3, 1, 7].length) (baseStart_3030879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3030879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3030879 prefixEnd_3030879 := by exact prefixLift 3030879
  have htrace : WordTrace (prefixWord ++ tailWord_3030879) baseStart_3030879 baseEnd_3030879 := by
    simpa [prefixWord, tailWord_3030879, baseEnd_3030879] using wordTrace_append hprefix tailTrace_3030879
  have hstable : (prefixWord ++ tailWord_3030879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3030879).length < 2 ^ (prefixWord ++ tailWord_3030879).sum := by decide
  have hdescent : baseEnd_3030879 < baseStart_3030879 := by decide
  rcases family_descends (prefixWord ++ tailWord_3030879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3030889 : List Nat := [1, 2, 1, 1, 1, 3, 1, 5, 2, 3, 3]
def baseStart_3030889 : Nat := 118140960795 + 3030889 * 2 ^ 59
def prefixEnd_3030889 : Nat := 4983230072969 + 3 ^ 40 * 3030889 * 2
def baseEnd_3030889 : Nat := 1556302867425097366548701

theorem tailTrace_3030889 : CollatzResearch.WordTrace tailWord_3030889 prefixEnd_3030889 1556302867425097366548701 := by
  unfold tailWord_3030889
  simp only [CollatzResearch.WordTrace]
  refine ⟨110545603516614262475311721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73697069011076174983541147 110545603516614262475311721)
  ·
    refine ⟨82909202637460696856483791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110545603516614262475311721 82909202637460696856483791)
    ·
      refine ⟨124363803956191045284725687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82909202637460696856483791 124363803956191045284725687)
      ·
        refine ⟨186545705934286567927088531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124363803956191045284725687 186545705934286567927088531)
        ·
          refine ⟨279818558901429851890632797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 186545705934286567927088531 279818558901429851890632797)
          ·
            refine ⟨104931959588036194458987299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 279818558901429851890632797 104931959588036194458987299)
            ·
              refine ⟨157397939382054291688480949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 104931959588036194458987299 157397939382054291688480949)
              ·
                refine ⟨14756056817067589845795089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 157397939382054291688480949 14756056817067589845795089)
                ·
                  refine ⟨11067042612800692384346317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14756056817067589845795089 11067042612800692384346317)
                  ·
                    refine ⟨4150140979800259644129869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11067042612800692384346317 4150140979800259644129869)
                    ·
                      refine ⟨1556302867425097366548701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4150140979800259644129869 1556302867425097366548701)
                      ·
                        rfl

theorem cell23_3030889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 5, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 5, 2, 3, 3].length) (baseStart_3030889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3030889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3030889 prefixEnd_3030889 := by exact prefixLift 3030889
  have htrace : WordTrace (prefixWord ++ tailWord_3030889) baseStart_3030889 baseEnd_3030889 := by
    simpa [prefixWord, tailWord_3030889, baseEnd_3030889] using wordTrace_append hprefix tailTrace_3030889
  have hstable : (prefixWord ++ tailWord_3030889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3030889).length < 2 ^ (prefixWord ++ tailWord_3030889).sum := by decide
  have hdescent : baseEnd_3030889 < baseStart_3030889 := by decide
  rcases family_descends (prefixWord ++ tailWord_3030889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3030930 : List Nat := [3, 2, 3, 2, 1, 1, 4, 2, 5]
def baseStart_3030930 : Nat := 118140960795 + 3030930 * 2 ^ 59
def prefixEnd_3030930 : Nat := 4983230072969 + 3 ^ 40 * 3030930 * 2
def baseEnd_3030930 : Nat := 172924880014659078459557

theorem tailTrace_3030930 : CollatzResearch.WordTrace tailWord_3030930 prefixEnd_3030930 172924880014659078459557 := by
  unfold tailWord_3030930
  simp only [CollatzResearch.WordTrace]
  refine ⟨27636774727366431619388561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73698065939643817651702829 27636774727366431619388561)
  ·
    refine ⟨20727581045524823714541421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27636774727366431619388561 20727581045524823714541421)
    ·
      refine ⟨7772842892071808892953033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20727581045524823714541421 7772842892071808892953033)
      ·
        refine ⟨5829632169053856669714775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7772842892071808892953033 5829632169053856669714775)
        ·
          refine ⟨8744448253580785004572163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5829632169053856669714775 8744448253580785004572163)
          ·
            refine ⟨13116672380371177506858245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8744448253580785004572163 13116672380371177506858245)
            ·
              refine ⟨2459376071319595782535921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13116672380371177506858245 2459376071319595782535921)
              ·
                refine ⟨1844532053489696836901941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2459376071319595782535921 1844532053489696836901941)
                ·
                  refine ⟨172924880014659078459557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1844532053489696836901941 172924880014659078459557)
                  ·
                    rfl

theorem cell23_3030930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 4, 2, 5].length) (baseStart_3030930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3030930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3030930 prefixEnd_3030930 := by exact prefixLift 3030930
  have htrace : WordTrace (prefixWord ++ tailWord_3030930) baseStart_3030930 baseEnd_3030930 := by
    simpa [prefixWord, tailWord_3030930, baseEnd_3030930] using wordTrace_append hprefix tailTrace_3030930
  have hstable : (prefixWord ++ tailWord_3030930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3030930).length < 2 ^ (prefixWord ++ tailWord_3030930).sum := by decide
  have hdescent : baseEnd_3030930 < baseStart_3030930 := by decide
  rcases family_descends (prefixWord ++ tailWord_3030930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3030969 : List Nat := [1, 2, 1, 4, 2, 1, 2, 2, 8]
def baseStart_3030969 : Nat := 118140960795 + 3030969 * 2 ^ 59
def prefixEnd_3030969 : Nat := 4983230072969 + 3 ^ 40 * 3030969 * 2
def baseEnd_3030969 : Nat := 172927105097495228172037

theorem tailTrace_3030969 : CollatzResearch.WordTrace tailWord_3030969 prefixEnd_3030969 172927105097495228172037 := by
  unfold tailWord_3030969
  simp only [CollatzResearch.WordTrace]
  refine ⟨110548521356324436138223961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73699014237549624092149307 110548521356324436138223961)
  ·
    refine ⟨82911391017243327103667971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110548521356324436138223961 82911391017243327103667971)
    ·
      refine ⟨124367086525864990655501957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82911391017243327103667971 124367086525864990655501957)
      ·
        refine ⟨23318828723599685747906617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 124367086525864990655501957 23318828723599685747906617)
        ·
          refine ⟨17489121542699764310929963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23318828723599685747906617 17489121542699764310929963)
          ·
            refine ⟨26233682314049646466394945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17489121542699764310929963 26233682314049646466394945)
            ·
              refine ⟨19675261735537234849796209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26233682314049646466394945 19675261735537234849796209)
              ·
                refine ⟨14756446301652926137347157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19675261735537234849796209 14756446301652926137347157)
                ·
                  refine ⟨172927105097495228172037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 14756446301652926137347157 172927105097495228172037)
                  ·
                    rfl

theorem cell23_3030969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 2, 2, 8].length) (baseStart_3030969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3030969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3030969 prefixEnd_3030969 := by exact prefixLift 3030969
  have htrace : WordTrace (prefixWord ++ tailWord_3030969) baseStart_3030969 baseEnd_3030969 := by
    simpa [prefixWord, tailWord_3030969, baseEnd_3030969] using wordTrace_append hprefix tailTrace_3030969
  have hstable : (prefixWord ++ tailWord_3030969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3030969).length < 2 ^ (prefixWord ++ tailWord_3030969).sum := by decide
  have hdescent : baseEnd_3030969 < baseStart_3030969 := by decide
  rcases family_descends (prefixWord ++ tailWord_3030969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3030986 : List Nat := [3, 1, 2, 1, 2, 1, 5, 2, 6]
def baseStart_3030986 : Nat := 118140960795 + 3030986 * 2 ^ 59
def prefixEnd_3030986 : Nat := 4983230072969 + 3 ^ 40 * 3030986 * 2
def baseEnd_3030986 : Nat := 172928075005398165226195

theorem tailTrace_3030986 : CollatzResearch.WordTrace tailWord_3030986 prefixEnd_3030986 172928075005398165226195 := by
  unfold tailWord_3030986
  simp only [CollatzResearch.WordTrace]
  refine ⟨27637285349315712010398203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73699427598175232027728541 27637285349315712010398203)
  ·
    refine ⟨41455928023973568015597305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27637285349315712010398203 41455928023973568015597305)
    ·
      refine ⟨31091946017980176011697979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41455928023973568015597305 31091946017980176011697979)
      ·
        refine ⟨46637919026970264017546969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31091946017980176011697979 46637919026970264017546969)
        ·
          refine ⟨34978439270227698013160227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46637919026970264017546969 34978439270227698013160227)
          ·
            refine ⟨52467658905341547019740341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34978439270227698013160227 52467658905341547019740341)
            ·
              refine ⟨4918843022375770033100657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 52467658905341547019740341 4918843022375770033100657)
              ·
                refine ⟨3689132266781827524825493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4918843022375770033100657 3689132266781827524825493)
                ·
                  refine ⟨172928075005398165226195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3689132266781827524825493 172928075005398165226195)
                  ·
                    rfl

theorem cell23_3030986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 5, 2, 6].length) (baseStart_3030986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3030986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3030986 prefixEnd_3030986 := by exact prefixLift 3030986
  have htrace : WordTrace (prefixWord ++ tailWord_3030986) baseStart_3030986 baseEnd_3030986 := by
    simpa [prefixWord, tailWord_3030986, baseEnd_3030986] using wordTrace_append hprefix tailTrace_3030986
  have hstable : (prefixWord ++ tailWord_3030986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3030986).length < 2 ^ (prefixWord ++ tailWord_3030986).sum := by decide
  have hdescent : baseEnd_3030986 < baseStart_3030986 := by decide
  rcases family_descends (prefixWord ++ tailWord_3030986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3031009 : List Nat := [1, 2, 3, 1, 2, 1, 2, 1, 2, 1, 7]
def baseStart_3031009 : Nat := 118140960795 + 3031009 * 2 ^ 59
def prefixEnd_3031009 : Nat := 4983230072969 + 3 ^ 40 * 3031009 * 2
def baseEnd_3031009 : Nat := 1556364485103636897048149

theorem tailTrace_3031009 : CollatzResearch.WordTrace tailWord_3031009 prefixEnd_3031009 1556364485103636897048149 := by
  unfold tailWord_3031009
  simp only [CollatzResearch.WordTrace]
  refine ⟨110549980276179522969680081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73699986850786348646453387 110549980276179522969680081)
  ·
    refine ⟨82912485207134642227260061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110549980276179522969680081 82912485207134642227260061)
    ·
      refine ⟨31092181952675490835222523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82912485207134642227260061 31092181952675490835222523)
      ·
        refine ⟨46638272929013236252833785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31092181952675490835222523 46638272929013236252833785)
        ·
          refine ⟨34978704696759927189625339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46638272929013236252833785 34978704696759927189625339)
          ·
            refine ⟨52468057045139890784438009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34978704696759927189625339 52468057045139890784438009)
            ·
              refine ⟨39351042783854918088328507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52468057045139890784438009 39351042783854918088328507)
              ·
                refine ⟨59026564175782377132492761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39351042783854918088328507 59026564175782377132492761)
                ·
                  refine ⟨44269923131836782849369571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 59026564175782377132492761 44269923131836782849369571)
                  ·
                    refine ⟨66404884697755174274054357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 44269923131836782849369571 66404884697755174274054357)
                    ·
                      refine ⟨1556364485103636897048149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 66404884697755174274054357 1556364485103636897048149)
                      ·
                        rfl

theorem cell23_3031009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 1, 2, 1, 7].length) (baseStart_3031009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3031009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3031009 prefixEnd_3031009 := by exact prefixLift 3031009
  have htrace : WordTrace (prefixWord ++ tailWord_3031009) baseStart_3031009 baseEnd_3031009 := by
    simpa [prefixWord, tailWord_3031009, baseEnd_3031009] using wordTrace_append hprefix tailTrace_3031009
  have hstable : (prefixWord ++ tailWord_3031009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3031009).length < 2 ^ (prefixWord ++ tailWord_3031009).sum := by decide
  have hdescent : baseEnd_3031009 < baseStart_3031009 := by decide
  rcases family_descends (prefixWord ++ tailWord_3031009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3031019 : List Nat := [1, 1, 1, 1, 2, 3, 1, 2, 2, 5, 4]
def baseStart_3031019 : Nat := 118140960795 + 3031019 * 2 ^ 59
def prefixEnd_3031019 : Nat := 4983230072969 + 3 ^ 40 * 3031019 * 2
def baseEnd_3031019 : Nat := 1556369619910181857923103

theorem tailTrace_3031019 : CollatzResearch.WordTrace tailWord_3031019 prefixEnd_3031019 1556369619910181857923103 := by
  unfold tailWord_3031019
  simp only [CollatzResearch.WordTrace]
  refine ⟨110550345006143294677544111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73700230004095529785029407 110550345006143294677544111)
  ·
    refine ⟨165825517509214942016316167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110550345006143294677544111 165825517509214942016316167)
    ·
      refine ⟨248738276263822413024474251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165825517509214942016316167 248738276263822413024474251)
      ·
        refine ⟨373107414395733619536711377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 248738276263822413024474251 373107414395733619536711377)
        ·
          refine ⟨279830560796800214652533533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 373107414395733619536711377 279830560796800214652533533)
          ·
            refine ⟨104936460298800080494700075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 279830560796800214652533533 104936460298800080494700075)
            ·
              refine ⟨157404690448200120742050113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 104936460298800080494700075 157404690448200120742050113)
              ·
                refine ⟨118053517836150090556537585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 157404690448200120742050113 118053517836150090556537585)
                ·
                  refine ⟨88540138377112567917403189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 118053517836150090556537585 88540138377112567917403189)
                  ·
                    refine ⟨8300637972854303242256549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 88540138377112567917403189 8300637972854303242256549)
                    ·
                      refine ⟨1556369619910181857923103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8300637972854303242256549 1556369619910181857923103)
                      ·
                        rfl

theorem cell23_3031019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 2, 2, 5, 4].length) (baseStart_3031019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3031019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3031019 prefixEnd_3031019 := by exact prefixLift 3031019
  have htrace : WordTrace (prefixWord ++ tailWord_3031019) baseStart_3031019 baseEnd_3031019 := by
    simpa [prefixWord, tailWord_3031019, baseEnd_3031019] using wordTrace_append hprefix tailTrace_3031019
  have hstable : (prefixWord ++ tailWord_3031019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3031019).length < 2 ^ (prefixWord ++ tailWord_3031019).sum := by decide
  have hdescent : baseEnd_3031019 < baseStart_3031019 := by decide
  rcases family_descends (prefixWord ++ tailWord_3031019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3031023 : List Nat := [1, 1, 2, 1, 4, 2, 2, 3, 2, 3, 2]
def baseStart_3031023 : Nat := 118140960795 + 3031023 * 2 ^ 59
def prefixEnd_3031023 : Nat := 4983230072969 + 3 ^ 40 * 3031023 * 2
def baseEnd_3031023 : Nat := 1556371673832799842273085

theorem tailTrace_3031023 : CollatzResearch.WordTrace tailWord_3031023 prefixEnd_3031023 1556371673832799842273085 := by
  unfold tailWord_3031023
  simp only [CollatzResearch.WordTrace]
  refine ⟨110550490898128803360689723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73700327265419202240459815 110550490898128803360689723)
  ·
    refine ⟨165825736347193205041034585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110550490898128803360689723 165825736347193205041034585)
    ·
      refine ⟨124369302260394903780775939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 165825736347193205041034585 124369302260394903780775939)
      ·
        refine ⟨186553953390592355671163909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124369302260394903780775939 186553953390592355671163909)
        ·
          refine ⟨34978866260736066688343233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 186553953390592355671163909 34978866260736066688343233)
          ·
            refine ⟨26234149695552050016257425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34978866260736066688343233 26234149695552050016257425)
            ·
              refine ⟨19675612271664037512193069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26234149695552050016257425 19675612271664037512193069)
              ·
                refine ⟨7378354601874014067072401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19675612271664037512193069 7378354601874014067072401)
                ·
                  refine ⟨5533765951405510550304301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7378354601874014067072401 5533765951405510550304301)
                  ·
                    refine ⟨2075162231777066456364113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5533765951405510550304301 2075162231777066456364113)
                    ·
                      refine ⟨1556371673832799842273085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2075162231777066456364113 1556371673832799842273085)
                      ·
                        rfl

theorem cell23_3031023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 2, 3, 2, 3, 2].length) (baseStart_3031023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3031023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3031023 prefixEnd_3031023 := by exact prefixLift 3031023
  have htrace : WordTrace (prefixWord ++ tailWord_3031023) baseStart_3031023 baseEnd_3031023 := by
    simpa [prefixWord, tailWord_3031023, baseEnd_3031023] using wordTrace_append hprefix tailTrace_3031023
  have hstable : (prefixWord ++ tailWord_3031023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3031023).length < 2 ^ (prefixWord ++ tailWord_3031023).sum := by decide
  have hdescent : baseEnd_3031023 < baseStart_3031023 := by decide
  rcases family_descends (prefixWord ++ tailWord_3031023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3031056 : List Nat := [2, 1, 1, 1, 1, 1, 1, 5, 5, 2, 3]
def baseStart_3031056 : Nat := 118140960795 + 3031056 * 2 ^ 59
def prefixEnd_3031056 : Nat := 4983230072969 + 3 ^ 40 * 3031056 * 2
def baseEnd_3031056 : Nat := 1556388618694398213160433

theorem tailTrace_3031056 : CollatzResearch.WordTrace tailWord_3031056 prefixEnd_3031056 1556388618694398213160433 := by
  unfold tailWord_3031056
  simp only [CollatzResearch.WordTrace]
  refine ⟨55275847253504624998320511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73701129671339499997760681 55275847253504624998320511)
  ·
    refine ⟨82913770880256937497480767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55275847253504624998320511 82913770880256937497480767)
    ·
      refine ⟨124370656320385406246221151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82913770880256937497480767 124370656320385406246221151)
      ·
        refine ⟨186555984480578109369331727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124370656320385406246221151 186555984480578109369331727)
        ·
          refine ⟨279833976720867164053997591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 186555984480578109369331727 279833976720867164053997591)
          ·
            refine ⟨419750965081300746080996387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 279833976720867164053997591 419750965081300746080996387)
            ·
              refine ⟨629626447621951119121494581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 419750965081300746080996387 629626447621951119121494581)
              ·
                refine ⟨59027479464557917417640117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 629626447621951119121494581 59027479464557917417640117)
                ·
                  refine ⟨5533826199802304757903761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 59027479464557917417640117 5533826199802304757903761)
                  ·
                    refine ⟨4150369649851728568427821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5533826199802304757903761 4150369649851728568427821)
                    ·
                      refine ⟨1556388618694398213160433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4150369649851728568427821 1556388618694398213160433)
                      ·
                        rfl

theorem cell23_3031056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 5, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 5, 5, 2, 3].length) (baseStart_3031056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3031056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3031056 prefixEnd_3031056 := by exact prefixLift 3031056
  have htrace : WordTrace (prefixWord ++ tailWord_3031056) baseStart_3031056 baseEnd_3031056 := by
    simpa [prefixWord, tailWord_3031056, baseEnd_3031056] using wordTrace_append hprefix tailTrace_3031056
  have hstable : (prefixWord ++ tailWord_3031056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3031056).length < 2 ^ (prefixWord ++ tailWord_3031056).sum := by decide
  have hdescent : baseEnd_3031056 < baseStart_3031056 := by decide
  rcases family_descends (prefixWord ++ tailWord_3031056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3031059 : List Nat := [1, 1, 1, 2, 1, 4, 3, 10]
def baseStart_3031059 : Nat := 118140960795 + 3031059 * 2 ^ 59
def prefixEnd_3031059 : Nat := 4983230072969 + 3 ^ 40 * 3031059 * 2
def baseEnd_3031059 : Nat := 57644079968013396348997

theorem tailTrace_3031059 : CollatzResearch.WordTrace tailWord_3031059 prefixEnd_3031059 57644079968013396348997 := by
  unfold tailWord_3031059
  simp only [CollatzResearch.WordTrace]
  refine ⟨110551803925998381509000231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73701202617332254339333487 110551803925998381509000231)
  ·
    refine ⟨165827705888997572263500347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110551803925998381509000231 165827705888997572263500347)
    ·
      refine ⟨248741558833496358395250521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165827705888997572263500347 248741558833496358395250521)
      ·
        refine ⟨186556169125122268796437891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 248741558833496358395250521 186556169125122268796437891)
        ·
          refine ⟨279834253687683403194656837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 186556169125122268796437891 279834253687683403194656837)
          ·
            refine ⟨52468922566440638098998157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 279834253687683403194656837 52468922566440638098998157)
            ·
              refine ⟨19675845962415239287124309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52468922566440638098998157 19675845962415239287124309)
              ·
                refine ⟨57644079968013396348997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 19675845962415239287124309 57644079968013396348997)
                ·
                  rfl

theorem cell23_3031059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 3, 10].length) (baseStart_3031059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3031059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3031059 prefixEnd_3031059 := by exact prefixLift 3031059
  have htrace : WordTrace (prefixWord ++ tailWord_3031059) baseStart_3031059 baseEnd_3031059 := by
    simpa [prefixWord, tailWord_3031059, baseEnd_3031059] using wordTrace_append hprefix tailTrace_3031059
  have hstable : (prefixWord ++ tailWord_3031059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3031059).length < 2 ^ (prefixWord ++ tailWord_3031059).sum := by decide
  have hdescent : baseEnd_3031059 < baseStart_3031059 := by decide
  rcases family_descends (prefixWord ++ tailWord_3031059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3031066 : List Nat := [3, 1, 1, 3, 1, 3, 2, 1, 1, 1, 6]
def baseStart_3031066 : Nat := 118140960795 + 3031066 * 2 ^ 59
def prefixEnd_3031066 : Nat := 4983230072969 + 3 ^ 40 * 3031066 * 2
def baseEnd_3031066 : Nat := 1556393753500943174035387

theorem tailTrace_3031066 : CollatzResearch.WordTrace tailWord_3031066 prefixEnd_3031066 1556393753500943174035387 := by
  unfold tailWord_3031066
  simp only [CollatzResearch.WordTrace]
  refine ⟨27638014809243255426126263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73701372824648681136336701 27638014809243255426126263)
  ·
    refine ⟨41457022213864883139189395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27638014809243255426126263 41457022213864883139189395)
    ·
      refine ⟨62185533320797324708784093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41457022213864883139189395 62185533320797324708784093)
      ·
        refine ⟨23319574995298996765794035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62185533320797324708784093 23319574995298996765794035)
        ·
          refine ⟨34979362492948495148691053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23319574995298996765794035 34979362492948495148691053)
          ·
            refine ⟨13117260934855685680759145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34979362492948495148691053 13117260934855685680759145)
            ·
              refine ⟨9837945701141764260569359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13117260934855685680759145 9837945701141764260569359)
              ·
                refine ⟨14756918551712646390854039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9837945701141764260569359 14756918551712646390854039)
                ·
                  refine ⟨22135377827568969586281059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14756918551712646390854039 22135377827568969586281059)
                  ·
                    refine ⟨33203066741353454379421589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22135377827568969586281059 33203066741353454379421589)
                    ·
                      refine ⟨1556393753500943174035387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 33203066741353454379421589 1556393753500943174035387)
                      ·
                        rfl

theorem cell23_3031066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 2, 1, 1, 1, 6].length) (baseStart_3031066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3031066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3031066 prefixEnd_3031066 := by exact prefixLift 3031066
  have htrace : WordTrace (prefixWord ++ tailWord_3031066) baseStart_3031066 baseEnd_3031066 := by
    simpa [prefixWord, tailWord_3031066, baseEnd_3031066] using wordTrace_append hprefix tailTrace_3031066
  have hstable : (prefixWord ++ tailWord_3031066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3031066).length < 2 ^ (prefixWord ++ tailWord_3031066).sum := by decide
  have hdescent : baseEnd_3031066 < baseStart_3031066 := by decide
  rcases family_descends (prefixWord ++ tailWord_3031066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3031080 : List Nat := [2, 1, 5, 3, 1, 1, 1, 2, 1, 6]
def baseStart_3031080 : Nat := 118140960795 + 3031080 * 2 ^ 59
def prefixEnd_3031080 : Nat := 4983230072969 + 3 ^ 40 * 3031080 * 2
def baseEnd_3031080 : Nat := 518800314076702039753441

theorem tailTrace_3031080 : CollatzResearch.WordTrace tailWord_3031080 prefixEnd_3031080 518800314076702039753441 := by
  unfold tailWord_3031080
  simp only [CollatzResearch.WordTrace]
  refine ⟨55276284929461151047757347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73701713239281534730343129 55276284929461151047757347)
  ·
    refine ⟨82914427394191726571636021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55276284929461151047757347 82914427394191726571636021)
    ·
      refine ⟨7773227568205474366090877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 82914427394191726571636021 7773227568205474366090877)
      ·
        refine ⟨2914960338077052887284079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7773227568205474366090877 2914960338077052887284079)
        ·
          refine ⟨4372440507115579330926119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2914960338077052887284079 4372440507115579330926119)
          ·
            refine ⟨6558660760673368996389179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4372440507115579330926119 6558660760673368996389179)
            ·
              refine ⟨9837991141010053494583769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6558660760673368996389179 9837991141010053494583769)
              ·
                refine ⟨7378493355757540120937827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9837991141010053494583769 7378493355757540120937827)
                ·
                  refine ⟨11067740033636310181406741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7378493355757540120937827 11067740033636310181406741)
                  ·
                    refine ⟨518800314076702039753441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11067740033636310181406741 518800314076702039753441)
                    ·
                      rfl

theorem cell23_3031080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 1, 2, 1, 6].length) (baseStart_3031080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3031080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3031080 prefixEnd_3031080 := by exact prefixLift 3031080
  have htrace : WordTrace (prefixWord ++ tailWord_3031080) baseStart_3031080 baseEnd_3031080 := by
    simpa [prefixWord, tailWord_3031080, baseEnd_3031080] using wordTrace_append hprefix tailTrace_3031080
  have hstable : (prefixWord ++ tailWord_3031080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3031080).length < 2 ^ (prefixWord ++ tailWord_3031080).sum := by decide
  have hdescent : baseEnd_3031080 < baseStart_3031080 := by decide
  rcases family_descends (prefixWord ++ tailWord_3031080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3031103 : List Nat := [1, 1, 2, 2, 3, 1, 2, 3, 4, 1, 3]
def baseStart_3031103 : Nat := 118140960795 + 3031103 * 2 ^ 59
def prefixEnd_3031103 : Nat := 4983230072969 + 3 ^ 40 * 3031103 * 2
def baseEnd_3031103 : Nat := 1556412752285159529272717

theorem tailTrace_3031103 : CollatzResearch.WordTrace tailWord_3031103 prefixEnd_3031103 1556412752285159529272717 := by
  unfold tailWord_3031103
  simp only [CollatzResearch.WordTrace]
  refine ⟨110553408737838977023601963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73702272491892651349067975 110553408737838977023601963)
  ·
    refine ⟨165830113106758465535402945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110553408737838977023601963 165830113106758465535402945)
    ·
      refine ⟨124372584830068849151552209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 165830113106758465535402945 124372584830068849151552209)
      ·
        refine ⟨93279438622551636863664157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 124372584830068849151552209 93279438622551636863664157)
        ·
          refine ⟨34979789483456863823874059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 93279438622551636863664157 34979789483456863823874059)
          ·
            refine ⟨52469684225185295735811089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34979789483456863823874059 52469684225185295735811089)
            ·
              refine ⟨39352263168888971801858317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52469684225185295735811089 39352263168888971801858317)
              ·
                refine ⟨14757098688333364425696869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39352263168888971801858317 14757098688333364425696869)
                ·
                  refine ⟨2766956004062505829818163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14757098688333364425696869 2766956004062505829818163)
                  ·
                    refine ⟨4150434006093758744727245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2766956004062505829818163 4150434006093758744727245)
                    ·
                      refine ⟨1556412752285159529272717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4150434006093758744727245 1556412752285159529272717)
                      ·
                        rfl

theorem cell23_3031103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 3, 4, 1, 3].length) (baseStart_3031103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3031103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3031103 prefixEnd_3031103 := by exact prefixLift 3031103
  have htrace : WordTrace (prefixWord ++ tailWord_3031103) baseStart_3031103 baseEnd_3031103 := by
    simpa [prefixWord, tailWord_3031103, baseEnd_3031103] using wordTrace_append hprefix tailTrace_3031103
  have hstable : (prefixWord ++ tailWord_3031103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3031103).length < 2 ^ (prefixWord ++ tailWord_3031103).sum := by decide
  have hdescent : baseEnd_3031103 < baseStart_3031103 := by decide
  rcases family_descends (prefixWord ++ tailWord_3031103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3031104 : List Nat := [2, 1, 1, 2, 2, 4, 4, 2, 1, 2, 2]
def baseStart_3031104 : Nat := 118140960795 + 3031104 * 2 ^ 59
def prefixEnd_3031104 : Nat := 4983230072969 + 3 ^ 40 * 3031104 * 2
def baseEnd_3031104 : Nat := 1556413265765814025360213

theorem tailTrace_3031104 : CollatzResearch.WordTrace tailWord_3031104 prefixEnd_3031104 1556413265765814025360213 := by
  unfold tailWord_3031104
  simp only [CollatzResearch.WordTrace]
  refine ⟨55276722605417677097194183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73702296807223569462925577 55276722605417677097194183)
  ·
    refine ⟨82915083908126515645791275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55276722605417677097194183 82915083908126515645791275)
    ·
      refine ⟨124372625862189773468686913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82915083908126515645791275 124372625862189773468686913)
      ·
        refine ⟨93279469396642330101515185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 124372625862189773468686913 93279469396642330101515185)
        ·
          refine ⟨69959602047481747576136389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93279469396642330101515185 69959602047481747576136389)
          ·
            refine ⟨13117425383902827670525573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 69959602047481747576136389 13117425383902827670525573)
            ·
              refine ⟨2459517259481780188223545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13117425383902827670525573 2459517259481780188223545)
              ·
                refine ⟨1844637944611335141167659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2459517259481780188223545 1844637944611335141167659)
                ·
                  refine ⟨2766956916917002711751489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1844637944611335141167659 2766956916917002711751489)
                  ·
                    refine ⟨2075217687687752033813617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2766956916917002711751489 2075217687687752033813617)
                    ·
                      refine ⟨1556413265765814025360213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2075217687687752033813617 1556413265765814025360213)
                      ·
                        rfl

theorem cell23_3031104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 4, 2, 1, 2, 2].length) (baseStart_3031104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3031104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3031104 prefixEnd_3031104 := by exact prefixLift 3031104
  have htrace : WordTrace (prefixWord ++ tailWord_3031104) baseStart_3031104 baseEnd_3031104 := by
    simpa [prefixWord, tailWord_3031104, baseEnd_3031104] using wordTrace_append hprefix tailTrace_3031104
  have hstable : (prefixWord ++ tailWord_3031104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3031104).length < 2 ^ (prefixWord ++ tailWord_3031104).sum := by decide
  have hdescent : baseEnd_3031104 < baseStart_3031104 := by decide
  rcases family_descends (prefixWord ++ tailWord_3031104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3031113 : List Nat := [1, 2, 1, 1, 2, 2, 3, 1, 5, 3, 2]
def baseStart_3031113 : Nat := 118140960795 + 3031113 * 2 ^ 59
def prefixEnd_3031113 : Nat := 4983230072969 + 3 ^ 40 * 3031113 * 2
def baseEnd_3031113 : Nat := 1556417887091704490147671

theorem tailTrace_3031113 : CollatzResearch.WordTrace tailWord_3031113 prefixEnd_3031113 1556417887091704490147671 := by
  unfold tailWord_3031113
  simp only [CollatzResearch.WordTrace]
  refine ⟨110553773467802748731465993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73702515645201832487643995 110553773467802748731465993)
  ·
    refine ⟨82915330100852061548599495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110553773467802748731465993 82915330100852061548599495)
    ·
      refine ⟨124372995151278092322899243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82915330100852061548599495 124372995151278092322899243)
      ·
        refine ⟨186559492726917138484348865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124372995151278092322899243 186559492726917138484348865)
        ·
          refine ⟨139919619545187853863261649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 186559492726917138484348865 139919619545187853863261649)
          ·
            refine ⟨104939714658890890397446237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 139919619545187853863261649 104939714658890890397446237)
            ·
              refine ⟨39352392997084083899042339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 104939714658890890397446237 39352392997084083899042339)
              ·
                refine ⟨59028589495626125848563509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39352392997084083899042339 59028589495626125848563509)
                ·
                  refine ⟨5533930265214949298302829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 59028589495626125848563509 5533930265214949298302829)
                  ·
                    refine ⟨2075223849455605986863561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5533930265214949298302829 2075223849455605986863561)
                    ·
                      refine ⟨1556417887091704490147671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2075223849455605986863561 1556417887091704490147671)
                      ·
                        rfl

theorem cell23_3031113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 1, 5, 3, 2].length) (baseStart_3031113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3031113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3031113 prefixEnd_3031113 := by exact prefixLift 3031113
  have htrace : WordTrace (prefixWord ++ tailWord_3031113) baseStart_3031113 baseEnd_3031113 := by
    simpa [prefixWord, tailWord_3031113, baseEnd_3031113] using wordTrace_append hprefix tailTrace_3031113
  have hstable : (prefixWord ++ tailWord_3031113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3031113).length < 2 ^ (prefixWord ++ tailWord_3031113).sum := by decide
  have hdescent : baseEnd_3031113 < baseStart_3031113 := by decide
  rcases family_descends (prefixWord ++ tailWord_3031113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3031130 : List Nat := [3, 1, 1, 2, 1, 1, 4, 4, 1, 3, 2]
def baseStart_3031130 : Nat := 118140960795 + 3031130 * 2 ^ 59
def prefixEnd_3031130 : Nat := 4983230072969 + 3 ^ 40 * 3031130 * 2
def baseEnd_3031130 : Nat := 1556426616262830923635093

theorem tailTrace_3031130 : CollatzResearch.WordTrace tailWord_3031130 prefixEnd_3031130 1556426616262830923635093 := by
  unfold tailWord_3031130
  simp only [CollatzResearch.WordTrace]
  refine ⟨27638598377185290158708711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73702929005827440423223229 27638598377185290158708711)
  ·
    refine ⟨41457897565777935238063067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27638598377185290158708711 41457897565777935238063067)
    ·
      refine ⟨62186846348666902857094601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41457897565777935238063067 62186846348666902857094601)
      ·
        refine ⟨46640134761500177142820951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62186846348666902857094601 46640134761500177142820951)
        ·
          refine ⟨69960202142250265714231427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46640134761500177142820951 69960202142250265714231427)
          ·
            refine ⟨104940303213375398571347141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69960202142250265714231427 104940303213375398571347141)
            ·
              refine ⟨19676306852507887232127589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 104940303213375398571347141 19676306852507887232127589)
              ·
                refine ⟨3689307534845228856023923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19676306852507887232127589 3689307534845228856023923)
                ·
                  refine ⟨5533961302267843284035885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3689307534845228856023923 5533961302267843284035885)
                  ·
                    refine ⟨2075235488350441231513457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5533961302267843284035885 2075235488350441231513457)
                    ·
                      refine ⟨1556426616262830923635093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2075235488350441231513457 1556426616262830923635093)
                      ·
                        rfl

theorem cell23_3031130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 4, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 4, 4, 1, 3, 2].length) (baseStart_3031130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3031130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3031130 prefixEnd_3031130 := by exact prefixLift 3031130
  have htrace : WordTrace (prefixWord ++ tailWord_3031130) baseStart_3031130 baseEnd_3031130 := by
    simpa [prefixWord, tailWord_3031130, baseEnd_3031130] using wordTrace_append hprefix tailTrace_3031130
  have hstable : (prefixWord ++ tailWord_3031130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3031130).length < 2 ^ (prefixWord ++ tailWord_3031130).sum := by decide
  have hdescent : baseEnd_3031130 < baseStart_3031130 := by decide
  rcases family_descends (prefixWord ++ tailWord_3031130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3031173 : List Nat := [1, 3, 1, 1, 5, 1, 2, 1, 2, 2, 4]
def baseStart_3031173 : Nat := 118140960795 + 3031173 * 2 ^ 59
def prefixEnd_3031173 : Nat := 4983230072969 + 3 ^ 40 * 3031173 * 2
def baseEnd_3031173 : Nat := 1556448695930974255397395

theorem tailTrace_3031173 : CollatzResearch.WordTrace tailWord_3031173 prefixEnd_3031173 1556448695930974255397395 := by
  unfold tailWord_3031173
  simp only [CollatzResearch.WordTrace]
  refine ⟨110555961847585378978650173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73703974565056919319100115 110555961847585378978650173)
  ·
    refine ⟨41458485692844517116993815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 110555961847585378978650173 41458485692844517116993815)
    ·
      refine ⟨62187728539266775675490723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41458485692844517116993815 62187728539266775675490723)
      ·
        refine ⟨93281592808900163513236085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62187728539266775675490723 93281592808900163513236085)
        ·
          refine ⟨8745149325834390329365883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 93281592808900163513236085 8745149325834390329365883)
          ·
            refine ⟨13117723988751585494048825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8745149325834390329365883 13117723988751585494048825)
            ·
              refine ⟨9838292991563689120536619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13117723988751585494048825 9838292991563689120536619)
              ·
                refine ⟨14757439487345533680804929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9838292991563689120536619 14757439487345533680804929)
                ·
                  refine ⟨11068079615509150260603697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14757439487345533680804929 11068079615509150260603697)
                  ·
                    refine ⟨8301059711631862695452773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11068079615509150260603697 8301059711631862695452773)
                    ·
                      refine ⟨1556448695930974255397395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8301059711631862695452773 1556448695930974255397395)
                      ·
                        rfl

theorem cell23_3031173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 2, 1, 2, 2, 4].length) (baseStart_3031173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3031173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3031173 prefixEnd_3031173 := by exact prefixLift 3031173
  have htrace : WordTrace (prefixWord ++ tailWord_3031173) baseStart_3031173 baseEnd_3031173 := by
    simpa [prefixWord, tailWord_3031173, baseEnd_3031173] using wordTrace_append hprefix tailTrace_3031173
  have hstable : (prefixWord ++ tailWord_3031173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3031173).length < 2 ^ (prefixWord ++ tailWord_3031173).sum := by decide
  have hdescent : baseEnd_3031173 < baseStart_3031173 := by decide
  rcases family_descends (prefixWord ++ tailWord_3031173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3031200 : List Nat := [2, 1, 1, 4, 2, 2, 3, 3, 5]
def baseStart_3031200 : Nat := 118140960795 + 3031200 * 2 ^ 59
def prefixEnd_3031200 : Nat := 4983230072969 + 3 ^ 40 * 3031200 * 2
def baseEnd_3031200 : Nat := 172940284434293961084419

theorem tailTrace_3031200 : CollatzResearch.WordTrace tailWord_3031200 prefixEnd_3031200 172940284434293961084419 := by
  unfold tailWord_3031200
  simp only [CollatzResearch.WordTrace]
  refine ⟨55278473309243781294941527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73704631078991708393255369 55278473309243781294941527)
  ·
    refine ⟨82917709963865671942412291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55278473309243781294941527 82917709963865671942412291)
    ·
      refine ⟨124376564945798507913618437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82917709963865671942412291 124376564945798507913618437)
      ·
        refine ⟨23320605927337220233803457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 124376564945798507913618437 23320605927337220233803457)
        ·
          refine ⟨17490454445502915175352593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23320605927337220233803457 17490454445502915175352593)
          ·
            refine ⟨13117840834127186381514445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17490454445502915175352593 13117840834127186381514445)
            ·
              refine ⟨4919190312797694893067917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13117840834127186381514445 4919190312797694893067917)
              ·
                refine ⟨1844696367299135584900469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4919190312797694893067917 1844696367299135584900469)
                ·
                  refine ⟨172940284434293961084419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1844696367299135584900469 172940284434293961084419)
                  ·
                    rfl

theorem cell23_3031200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 3, 3, 5].length) (baseStart_3031200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3031200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3031200 prefixEnd_3031200 := by exact prefixLift 3031200
  have htrace : WordTrace (prefixWord ++ tailWord_3031200) baseStart_3031200 baseEnd_3031200 := by
    simpa [prefixWord, tailWord_3031200, baseEnd_3031200] using wordTrace_append hprefix tailTrace_3031200
  have hstable : (prefixWord ++ tailWord_3031200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3031200).length < 2 ^ (prefixWord ++ tailWord_3031200).sum := by decide
  have hdescent : baseEnd_3031200 < baseStart_3031200 := by decide
  rcases family_descends (prefixWord ++ tailWord_3031200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3031203 : List Nat := [1, 1, 1, 4, 1, 1, 1, 1, 3, 7, 2]
def baseStart_3031203 : Nat := 118140960795 + 3031203 * 2 ^ 59
def prefixEnd_3031203 : Nat := 4983230072969 + 3 ^ 40 * 3031203 * 2
def baseEnd_3031203 : Nat := 1556464100350609138022257

theorem tailTrace_3031203 : CollatzResearch.WordTrace tailWord_3031203 prefixEnd_3031203 1556464100350609138022257 := by
  unfold tailWord_3031203
  simp only [CollatzResearch.WordTrace]
  refine ⟨110557056037476694102242263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73704704024984462734828175 110557056037476694102242263)
  ·
    refine ⟨165835584056215041153363395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110557056037476694102242263 165835584056215041153363395)
    ·
      refine ⟨248753376084322561730045093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165835584056215041153363395 248753376084322561730045093)
      ·
        refine ⟨46641258015810480324383455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 248753376084322561730045093 46641258015810480324383455)
        ·
          refine ⟨69961887023715720486575183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46641258015810480324383455 69961887023715720486575183)
          ·
            refine ⟨104942830535573580729862775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69961887023715720486575183 104942830535573580729862775)
            ·
              refine ⟨157414245803360371094794163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 104942830535573580729862775 157414245803360371094794163)
              ·
                refine ⟨236121368705040556642191245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 157414245803360371094794163 236121368705040556642191245)
                ·
                  refine ⟨88545513264390208740821717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 236121368705040556642191245 88545513264390208740821717)
                  ·
                    refine ⟨2075285467134145517363009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 88545513264390208740821717 2075285467134145517363009)
                    ·
                      refine ⟨1556464100350609138022257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2075285467134145517363009 1556464100350609138022257)
                      ·
                        rfl

theorem cell23_3031203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 1, 3, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 1, 3, 7, 2].length) (baseStart_3031203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3031203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3031203 prefixEnd_3031203 := by exact prefixLift 3031203
  have htrace : WordTrace (prefixWord ++ tailWord_3031203) baseStart_3031203 baseEnd_3031203 := by
    simpa [prefixWord, tailWord_3031203, baseEnd_3031203] using wordTrace_append hprefix tailTrace_3031203
  have hstable : (prefixWord ++ tailWord_3031203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3031203).length < 2 ^ (prefixWord ++ tailWord_3031203).sum := by decide
  have hdescent : baseEnd_3031203 < baseStart_3031203 := by decide
  rcases family_descends (prefixWord ++ tailWord_3031203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3031217 : List Nat := [1, 2, 2, 5, 3, 1, 1, 1, 7]
def baseStart_3031217 : Nat := 118140960795 + 3031217 * 2 ^ 59
def prefixEnd_3031217 : Nat := 4983230072969 + 3 ^ 40 * 3031217 * 2
def baseEnd_3031217 : Nat := 172941254342196898138577

theorem tailTrace_3031217 : CollatzResearch.WordTrace tailWord_3031217 prefixEnd_3031217 172941254342196898138577 := by
  unfold tailWord_3031217
  simp only [CollatzResearch.WordTrace]
  refine ⟨110557566659425974493251905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73705044439617316328834603 110557566659425974493251905)
  ·
    refine ⟨82918174994569480869938929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110557566659425974493251905 82918174994569480869938929)
    ·
      refine ⟨62188631245927110652454197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82918174994569480869938929 62188631245927110652454197)
      ·
        refine ⟨5830184179305666623667581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 62188631245927110652454197 5830184179305666623667581)
        ·
          refine ⟨2186319067239624983875343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5830184179305666623667581 2186319067239624983875343)
          ·
            refine ⟨3279478600859437475813015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2186319067239624983875343 3279478600859437475813015)
            ·
              refine ⟨4919217901289156213719523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3279478600859437475813015 4919217901289156213719523)
              ·
                refine ⟨7378826851933734320579285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4919217901289156213719523 7378826851933734320579285)
                ·
                  refine ⟨172941254342196898138577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7378826851933734320579285 172941254342196898138577)
                  ·
                    rfl

theorem cell23_3031217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 3, 1, 1, 1, 7].length) (baseStart_3031217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3031217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3031217 prefixEnd_3031217 := by exact prefixLift 3031217
  have htrace : WordTrace (prefixWord ++ tailWord_3031217) baseStart_3031217 baseEnd_3031217 := by
    simpa [prefixWord, tailWord_3031217, baseEnd_3031217] using wordTrace_append hprefix tailTrace_3031217
  have hstable : (prefixWord ++ tailWord_3031217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3031217).length < 2 ^ (prefixWord ++ tailWord_3031217).sum := by decide
  have hdescent : baseEnd_3031217 < baseStart_3031217 := by decide
  rcases family_descends (prefixWord ++ tailWord_3031217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3031223 : List Nat := [1, 1, 3, 1, 4, 3, 1, 1, 1, 2, 5]
def baseStart_3031223 : Nat := 118140960795 + 3031223 * 2 ^ 59
def prefixEnd_3031223 : Nat := 4983230072969 + 3 ^ 40 * 3031223 * 2
def baseEnd_3031223 : Nat := 1556474369963699059772165

theorem tailTrace_3031223 : CollatzResearch.WordTrace tailWord_3031223 prefixEnd_3031223 1556474369963699059772165 := by
  unfold tailWord_3031223
  simp only [CollatzResearch.WordTrace]
  refine ⟨110557785497404237517970323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73705190331602825011980215 110557785497404237517970323)
  ·
    refine ⟨165836678246106356276955485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110557785497404237517970323 165836678246106356276955485)
    ·
      refine ⟨62188754342289883603858307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 165836678246106356276955485 62188754342289883603858307)
      ·
        refine ⟨93283131513434825405787461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62188754342289883603858307 93283131513434825405787461)
        ·
          refine ⟨17490587158769029763585149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 93283131513434825405787461 17490587158769029763585149)
          ·
            refine ⟨6558970184538386161344431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17490587158769029763585149 6558970184538386161344431)
            ·
              refine ⟨9838455276807579242016647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6558970184538386161344431 9838455276807579242016647)
              ·
                refine ⟨14757682915211368863024971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9838455276807579242016647 14757682915211368863024971)
                ·
                  refine ⟨22136524372817053294537457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14757682915211368863024971 22136524372817053294537457)
                  ·
                    refine ⟨16602393279612789970903093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22136524372817053294537457 16602393279612789970903093)
                    ·
                      refine ⟨1556474369963699059772165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16602393279612789970903093 1556474369963699059772165)
                      ·
                        rfl

theorem cell23_3031223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 1, 1, 1, 2, 5].length) (baseStart_3031223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3031223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3031223 prefixEnd_3031223 := by exact prefixLift 3031223
  have htrace : WordTrace (prefixWord ++ tailWord_3031223) baseStart_3031223 baseEnd_3031223 := by
    simpa [prefixWord, tailWord_3031223, baseEnd_3031223] using wordTrace_append hprefix tailTrace_3031223
  have hstable : (prefixWord ++ tailWord_3031223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3031223).length < 2 ^ (prefixWord ++ tailWord_3031223).sum := by decide
  have hdescent : baseEnd_3031223 < baseStart_3031223 := by decide
  rcases family_descends (prefixWord ++ tailWord_3031223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3031228 : List Nat := [2, 2, 2, 3, 4, 1, 2, 1, 2, 2, 2]
def baseStart_3031228 : Nat := 118140960795 + 3031228 * 2 ^ 59
def prefixEnd_3031228 : Nat := 4983230072969 + 3 ^ 40 * 3031228 * 2
def baseEnd_3031228 : Nat := 1556476937366971540209643

theorem tailTrace_3031228 : CollatzResearch.WordTrace tailWord_3031228 prefixEnd_3031228 1556476937366971540209643 := by
  unfold tailWord_3031228
  simp only [CollatzResearch.WordTrace]
  refine ⟨55278983931193061685951169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73705311908257415581268225 55278983931193061685951169)
  ·
    refine ⟨41459237948394796264463377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55278983931193061685951169 41459237948394796264463377)
    ·
      refine ⟨31094428461296097198347533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41459237948394796264463377 31094428461296097198347533)
      ·
        refine ⟨11660410672986036449380325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31094428461296097198347533 11660410672986036449380325)
        ·
          refine ⟨2186327001184881834258811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11660410672986036449380325 2186327001184881834258811)
          ·
            refine ⟨3279490501777322751388217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2186327001184881834258811 3279490501777322751388217)
            ·
              refine ⟨2459617876332992063541163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3279490501777322751388217 2459617876332992063541163)
              ·
                refine ⟨3689426814499488095311745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2459617876332992063541163 3689426814499488095311745)
                ·
                  refine ⟨2767070110874616071483809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3689426814499488095311745 2767070110874616071483809)
                  ·
                    refine ⟨2075302583155962053612857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2767070110874616071483809 2075302583155962053612857)
                    ·
                      refine ⟨1556476937366971540209643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2075302583155962053612857 1556476937366971540209643)
                      ·
                        rfl

theorem cell23_3031228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 4, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 4, 1, 2, 1, 2, 2, 2].length) (baseStart_3031228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3031228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3031228 prefixEnd_3031228 := by exact prefixLift 3031228
  have htrace : WordTrace (prefixWord ++ tailWord_3031228) baseStart_3031228 baseEnd_3031228 := by
    simpa [prefixWord, tailWord_3031228, baseEnd_3031228] using wordTrace_append hprefix tailTrace_3031228
  have hstable : (prefixWord ++ tailWord_3031228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3031228).length < 2 ^ (prefixWord ++ tailWord_3031228).sum := by decide
  have hdescent : baseEnd_3031228 < baseStart_3031228 := by decide
  rcases family_descends (prefixWord ++ tailWord_3031228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3031243 : List Nat := [1, 1, 1, 1, 3, 2, 4, 1, 5, 4]
def baseStart_3031243 : Nat := 118140960795 + 3031243 * 2 ^ 59
def prefixEnd_3031243 : Nat := 4983230072969 + 3 ^ 40 * 3031243 * 2
def baseEnd_3031243 : Nat := 518828213192262993840691

theorem tailTrace_3031243 : CollatzResearch.WordTrace tailWord_3031243 prefixEnd_3031243 518828213192262993840691 := by
  unfold tailWord_3031243
  simp only [CollatzResearch.WordTrace]
  refine ⟨110558514957331780933698383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73705676638221187289132255 110558514957331780933698383)
  ·
    refine ⟨165837772435997671400547575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110558514957331780933698383 165837772435997671400547575)
    ·
      refine ⟨248756658653996507100821363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165837772435997671400547575 248756658653996507100821363)
      ·
        refine ⟨373134987980994760651232045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 248756658653996507100821363 373134987980994760651232045)
        ·
          refine ⟨139925620492873035244212017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 373134987980994760651232045 139925620492873035244212017)
          ·
            refine ⟨104944215369654776433159013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 139925620492873035244212017 104944215369654776433159013)
            ·
              refine ⟨19677040381810270581217315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 104944215369654776433159013 19677040381810270581217315)
              ·
                refine ⟨29515560572715405871825973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19677040381810270581217315 29515560572715405871825973)
                ·
                  refine ⟨2767083803692069300483685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 29515560572715405871825973 2767083803692069300483685)
                  ·
                    refine ⟨518828213192262993840691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2767083803692069300483685 518828213192262993840691)
                    ·
                      rfl

theorem cell23_3031243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 4, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 4, 1, 5, 4].length) (baseStart_3031243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3031243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3031243 prefixEnd_3031243 := by exact prefixLift 3031243
  have htrace : WordTrace (prefixWord ++ tailWord_3031243) baseStart_3031243 baseEnd_3031243 := by
    simpa [prefixWord, tailWord_3031243, baseEnd_3031243] using wordTrace_append hprefix tailTrace_3031243
  have hstable : (prefixWord ++ tailWord_3031243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3031243).length < 2 ^ (prefixWord ++ tailWord_3031243).sum := by decide
  have hdescent : baseEnd_3031243 < baseStart_3031243 := by decide
  rcases family_descends (prefixWord ++ tailWord_3031243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3031250 : List Nat := [3, 2, 2, 2, 1, 2, 1, 3, 2, 1, 4]
def baseStart_3031250 : Nat := 118140960795 + 3031250 * 2 ^ 59
def prefixEnd_3031250 : Nat := 4983230072969 + 3 ^ 40 * 3031250 * 2
def baseEnd_3031250 : Nat := 1556488233941370454134541

theorem tailTrace_3031250 : CollatzResearch.WordTrace tailWord_3031250 prefixEnd_3031250 1556488233941370454134541 := by
  unfold tailWord_3031250
  simp only [CollatzResearch.WordTrace]
  refine ⟨27639692567076605282300801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73705846845537614086135469 27639692567076605282300801)
  ·
    refine ⟨20729769425307453961725601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27639692567076605282300801 20729769425307453961725601)
    ·
      refine ⟨15547327068980590471294201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20729769425307453961725601 15547327068980590471294201)
      ·
        refine ⟨11660495301735442853470651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15547327068980590471294201 11660495301735442853470651)
        ·
          refine ⟨17490742952603164280205977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11660495301735442853470651 17490742952603164280205977)
          ·
            refine ⟨13118057214452373210154483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17490742952603164280205977 13118057214452373210154483)
            ·
              refine ⟨19677085821678559815231725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13118057214452373210154483 19677085821678559815231725)
              ·
                refine ⟨7378907183129459930711897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19677085821678559815231725 7378907183129459930711897)
                ·
                  refine ⟨5534180387347094948033923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7378907183129459930711897 5534180387347094948033923)
                  ·
                    refine ⟨8301270581020642422050885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5534180387347094948033923 8301270581020642422050885)
                    ·
                      refine ⟨1556488233941370454134541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8301270581020642422050885 1556488233941370454134541)
                      ·
                        rfl

theorem cell23_3031250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 1, 3, 2, 1, 4].length) (baseStart_3031250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3031250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3031250 prefixEnd_3031250 := by exact prefixLift 3031250
  have htrace : WordTrace (prefixWord ++ tailWord_3031250) baseStart_3031250 baseEnd_3031250 := by
    simpa [prefixWord, tailWord_3031250, baseEnd_3031250] using wordTrace_append hprefix tailTrace_3031250
  have hstable : (prefixWord ++ tailWord_3031250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3031250).length < 2 ^ (prefixWord ++ tailWord_3031250).sum := by decide
  have hdescent : baseEnd_3031250 < baseStart_3031250 := by decide
  rcases family_descends (prefixWord ++ tailWord_3031250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3031320 : List Nat := [2, 1, 2, 3, 1, 2, 3, 3, 1, 5]
def baseStart_3031320 : Nat := 118140960795 + 3031320 * 2 ^ 59
def prefixEnd_3031320 : Nat := 4983230072969 + 3 ^ 40 * 3031320 * 2
def baseEnd_3031320 : Nat := 518841392529061726753073

theorem tailTrace_3031320 : CollatzResearch.WordTrace tailWord_3031320 prefixEnd_3031320 518841392529061726753073 := by
  unfold tailWord_3031320
  simp only [CollatzResearch.WordTrace]
  refine ⟨55280661689026411542125707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73707548918701882056167609 55280661689026411542125707)
  ·
    refine ⟨82920992533539617313188561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55280661689026411542125707 82920992533539617313188561)
    ·
      refine ⟨62190744400154712984891421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82920992533539617313188561 62190744400154712984891421)
      ·
        refine ⟨23321529150058017369334283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62190744400154712984891421 23321529150058017369334283)
        ·
          refine ⟨34982293725087026054001425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23321529150058017369334283 34982293725087026054001425)
          ·
            refine ⟨26236720293815269540501069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34982293725087026054001425 26236720293815269540501069)
            ·
              refine ⟨9838770110180726077687901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26236720293815269540501069 9838770110180726077687901)
              ·
                refine ⟨3689538791317772279132963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9838770110180726077687901 3689538791317772279132963)
                ·
                  refine ⟨5534308186976658418699445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3689538791317772279132963 5534308186976658418699445)
                  ·
                    refine ⟨518841392529061726753073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5534308186976658418699445 518841392529061726753073)
                    ·
                      rfl

theorem cell23_3031320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 3, 3, 1, 5].length) (baseStart_3031320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3031320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3031320 prefixEnd_3031320 := by exact prefixLift 3031320
  have htrace : WordTrace (prefixWord ++ tailWord_3031320) baseStart_3031320 baseEnd_3031320 := by
    simpa [prefixWord, tailWord_3031320, baseEnd_3031320] using wordTrace_append hprefix tailTrace_3031320
  have hstable : (prefixWord ++ tailWord_3031320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3031320).length < 2 ^ (prefixWord ++ tailWord_3031320).sum := by decide
  have hdescent : baseEnd_3031320 < baseStart_3031320 := by decide
  rcases family_descends (prefixWord ++ tailWord_3031320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3031343 : List Nat := [1, 1, 2, 1, 2, 1, 5, 1, 3, 1, 5]
def baseStart_3031343 : Nat := 118140960795 + 3031343 * 2 ^ 59
def prefixEnd_3031343 : Nat := 4983230072969 + 3 ^ 40 * 3031343 * 2
def baseEnd_3031343 : Nat := 1556535987642238590271613

theorem tailTrace_3031343 : CollatzResearch.WordTrace tailWord_3031343 prefixEnd_3031343 1556535987642238590271613 := by
  unfold tailWord_3031343
  simp only [CollatzResearch.WordTrace]
  refine ⟨110562162256969498012338683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73708108171312998674892455 110562162256969498012338683)
  ·
    refine ⟨165843243385454247018508025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110562162256969498012338683 165843243385454247018508025)
    ·
      refine ⟨124382432539090685263881019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 165843243385454247018508025 124382432539090685263881019)
      ·
        refine ⟨186573648808636027895821529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124382432539090685263881019 186573648808636027895821529)
        ·
          refine ⟨139930236606477020921866147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 186573648808636027895821529 139930236606477020921866147)
          ·
            refine ⟨209895354909715531382799221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 139930236606477020921866147 209895354909715531382799221)
            ·
              refine ⟨19677689522785831067137427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 209895354909715531382799221 19677689522785831067137427)
              ·
                refine ⟨29516534284178746600706141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19677689522785831067137427 29516534284178746600706141)
                ·
                  refine ⟨11068700356567029975264803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29516534284178746600706141 11068700356567029975264803)
                  ·
                    refine ⟨16603050534850544962897205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11068700356567029975264803 16603050534850544962897205)
                    ·
                      refine ⟨1556535987642238590271613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16603050534850544962897205 1556535987642238590271613)
                      ·
                        rfl

theorem cell23_3031343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 5, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 5, 1, 3, 1, 5].length) (baseStart_3031343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3031343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3031343 prefixEnd_3031343 := by exact prefixLift 3031343
  have htrace : WordTrace (prefixWord ++ tailWord_3031343) baseStart_3031343 baseEnd_3031343 := by
    simpa [prefixWord, tailWord_3031343, baseEnd_3031343] using wordTrace_append hprefix tailTrace_3031343
  have hstable : (prefixWord ++ tailWord_3031343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3031343).length < 2 ^ (prefixWord ++ tailWord_3031343).sum := by decide
  have hdescent : baseEnd_3031343 < baseStart_3031343 := by decide
  rcases family_descends (prefixWord ++ tailWord_3031343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3031377 : List Nat := [1, 2, 2, 1, 4, 2, 2, 3, 1, 2, 3]
def baseStart_3031377 : Nat := 118140960795 + 3031377 * 2 ^ 59
def prefixEnd_3031377 : Nat := 4983230072969 + 3 ^ 40 * 3031377 * 2
def baseEnd_3031377 : Nat := 1556553445984491457246457

theorem tailTrace_3031377 : CollatzResearch.WordTrace tailWord_3031377 prefixEnd_3031377 1556553445984491457246457 := by
  unfold tailWord_3031377
  simp only [CollatzResearch.WordTrace]
  refine ⟨110563402338846321819076385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73708934892564214546050923 110563402338846321819076385)
  ·
    refine ⟨82922551754134741364307289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110563402338846321819076385 82922551754134741364307289)
    ·
      refine ⟨62191913815601056023230467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82922551754134741364307289 62191913815601056023230467)
      ·
        refine ⟨93287870723401584034845701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62191913815601056023230467 93287870723401584034845701)
        ·
          refine ⟨17491475760637797006533569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 93287870723401584034845701 17491475760637797006533569)
          ·
            refine ⟨13118606820478347754900177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17491475760637797006533569 13118606820478347754900177)
            ·
              refine ⟨9838955115358760816175133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13118606820478347754900177 9838955115358760816175133)
              ·
                refine ⟨3689608168259535306065675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9838955115358760816175133 3689608168259535306065675)
                ·
                  refine ⟨5534412252389302959098513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3689608168259535306065675 5534412252389302959098513)
                  ·
                    refine ⟨4150809189291977219323885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5534412252389302959098513 4150809189291977219323885)
                    ·
                      refine ⟨1556553445984491457246457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4150809189291977219323885 1556553445984491457246457)
                      ·
                        rfl

theorem cell23_3031377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 2, 3, 1, 2, 3].length) (baseStart_3031377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3031377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3031377 prefixEnd_3031377 := by exact prefixLift 3031377
  have htrace : WordTrace (prefixWord ++ tailWord_3031377) baseStart_3031377 baseEnd_3031377 := by
    simpa [prefixWord, tailWord_3031377, baseEnd_3031377] using wordTrace_append hprefix tailTrace_3031377
  have hstable : (prefixWord ++ tailWord_3031377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3031377).length < 2 ^ (prefixWord ++ tailWord_3031377).sum := by decide
  have hdescent : baseEnd_3031377 < baseStart_3031377 := by decide
  rcases family_descends (prefixWord ++ tailWord_3031377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3031380 : List Nat := [2, 4, 1, 1, 2, 4, 9]
def baseStart_3031380 : Nat := 118140960795 + 3031380 * 2 ^ 59
def prefixEnd_3031380 : Nat := 4983230072969 + 3 ^ 40 * 3031380 * 2
def baseEnd_3031380 : Nat := 19216728227487098092703

theorem tailTrace_3031380 : CollatzResearch.WordTrace tailWord_3031380 prefixEnd_3031380 19216728227487098092703 := by
  unfold tailWord_3031380
  simp only [CollatzResearch.WordTrace]
  refine ⟨55281755878917726665717797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73709007838556968887623729 55281755878917726665717797)
  ·
    refine ⟨10365329227297073749822087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 55281755878917726665717797 10365329227297073749822087)
    ·
      refine ⟨15547993840945610624733131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10365329227297073749822087 15547993840945610624733131)
      ·
        refine ⟨23321990761418415937099697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15547993840945610624733131 23321990761418415937099697)
        ·
          refine ⟨17491493071063811952824773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23321990761418415937099697 17491493071063811952824773)
          ·
            refine ⟨3279654950824464741154645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17491493071063811952824773 3279654950824464741154645)
            ·
              refine ⟨19216728227487098092703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3279654950824464741154645 19216728227487098092703)
              ·
                rfl

theorem cell23_3031380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 4, 9].length) (baseStart_3031380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3031380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3031380 prefixEnd_3031380 := by exact prefixLift 3031380
  have htrace : WordTrace (prefixWord ++ tailWord_3031380) baseStart_3031380 baseEnd_3031380 := by
    simpa [prefixWord, tailWord_3031380, baseEnd_3031380] using wordTrace_append hprefix tailTrace_3031380
  have hstable : (prefixWord ++ tailWord_3031380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3031380).length < 2 ^ (prefixWord ++ tailWord_3031380).sum := by decide
  have hdescent : baseEnd_3031380 < baseStart_3031380 := by decide
  rcases family_descends (prefixWord ++ tailWord_3031380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3031403 : List Nat := [1, 1, 1, 1, 2, 2, 2, 2, 4, 2, 5]
def baseStart_3031403 : Nat := 118140960795 + 3031403 * 2 ^ 59
def prefixEnd_3031403 : Nat := 4983230072969 + 3 ^ 40 * 3031403 * 2
def baseEnd_3031403 : Nat := 1556566796481508355521337

theorem tailTrace_3031403 : CollatzResearch.WordTrace tailWord_3031403 prefixEnd_3031403 1556566796481508355521337 := by
  unfold tailWord_3031403
  simp only [CollatzResearch.WordTrace]
  refine ⟨110564350636752128259522863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73709567091168085506348575 110564350636752128259522863)
  ·
    refine ⟨165846525955128192389284295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110564350636752128259522863 165846525955128192389284295)
    ·
      refine ⟨248769788932692288583926443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165846525955128192389284295 248769788932692288583926443)
      ·
        refine ⟨373154683399038432875889665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 248769788932692288583926443 373154683399038432875889665)
        ·
          refine ⟨279866012549278824656917249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 373154683399038432875889665 279866012549278824656917249)
          ·
            refine ⟨209899509411959118492687937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 279866012549278824656917249 209899509411959118492687937)
            ·
              refine ⟨157424632058969338869515953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 209899509411959118492687937 157424632058969338869515953)
              ·
                refine ⟨118068474044227004152136965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 157424632058969338869515953 118068474044227004152136965)
                ·
                  refine ⟨22137838883292563278525681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 118068474044227004152136965 22137838883292563278525681)
                  ·
                    refine ⟨16603379162469422458894261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22137838883292563278525681 16603379162469422458894261)
                    ·
                      refine ⟨1556566796481508355521337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16603379162469422458894261 1556566796481508355521337)
                      ·
                        rfl

theorem cell23_3031403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 4, 2, 5].length) (baseStart_3031403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3031403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3031403 prefixEnd_3031403 := by exact prefixLift 3031403
  have htrace : WordTrace (prefixWord ++ tailWord_3031403) baseStart_3031403 baseEnd_3031403 := by
    simpa [prefixWord, tailWord_3031403, baseEnd_3031403] using wordTrace_append hprefix tailTrace_3031403
  have hstable : (prefixWord ++ tailWord_3031403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3031403).length < 2 ^ (prefixWord ++ tailWord_3031403).sum := by decide
  have hdescent : baseEnd_3031403 < baseStart_3031403 := by decide
  rcases family_descends (prefixWord ++ tailWord_3031403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3031423 : List Nat := [1, 1, 2, 2, 1, 1, 2, 4, 1, 8]
def baseStart_3031423 : Nat := 118140960795 + 3031423 * 2 ^ 59
def prefixEnd_3031423 : Nat := 4983230072969 + 3 ^ 40 * 3031423 * 2
def baseEnd_3031423 : Nat := 518859022031532759090415

theorem tailTrace_3031423 : CollatzResearch.WordTrace tailWord_3031423 prefixEnd_3031423 518859022031532759090415 := by
  unfold tailWord_3031423
  simp only [CollatzResearch.WordTrace]
  refine ⟨110565080096679671675250923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73710053397786447783500615 110565080096679671675250923)
  ·
    refine ⟨165847620145019507512876385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110565080096679671675250923 165847620145019507512876385)
    ·
      refine ⟨124385715108764630634657289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 165847620145019507512876385 124385715108764630634657289)
      ·
        refine ⟨93289286331573472975992967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 124385715108764630634657289 93289286331573472975992967)
        ·
          refine ⟨139933929497360209463989451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93289286331573472975992967 139933929497360209463989451)
          ·
            refine ⟨209900894246040314195984177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 139933929497360209463989451 209900894246040314195984177)
            ·
              refine ⟨157425670684530235646988133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 209900894246040314195984177 157425670684530235646988133)
              ·
                refine ⟨29517313253349419183810275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 157425670684530235646988133 29517313253349419183810275)
                ·
                  refine ⟨44275969880024128775715413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29517313253349419183810275 44275969880024128775715413)
                  ·
                    refine ⟨518859022031532759090415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 44275969880024128775715413 518859022031532759090415)
                    ·
                      rfl

theorem cell23_3031423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 4, 1, 8].length) (baseStart_3031423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3031423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3031423 prefixEnd_3031423 := by exact prefixLift 3031423
  have htrace : WordTrace (prefixWord ++ tailWord_3031423) baseStart_3031423 baseEnd_3031423 := by
    simpa [prefixWord, tailWord_3031423, baseEnd_3031423] using wordTrace_append hprefix tailTrace_3031423
  have hstable : (prefixWord ++ tailWord_3031423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3031423).length < 2 ^ (prefixWord ++ tailWord_3031423).sum := by decide
  have hdescent : baseEnd_3031423 < baseStart_3031423 := by decide
  rcases family_descends (prefixWord ++ tailWord_3031423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3031460 : List Nat := [2, 3, 1, 2, 1, 1, 3, 1, 1, 4, 4]
def baseStart_3031460 : Nat := 118140960795 + 3031460 * 2 ^ 59
def prefixEnd_3031460 : Nat := 4983230072969 + 3 ^ 40 * 3031460 * 2
def baseEnd_3031460 : Nat := 1556596064878814632508575

theorem tailTrace_3031460 : CollatzResearch.WordTrace tailWord_3031460 prefixEnd_3031460 1556596064878814632508575 := by
  unfold tailWord_3031460
  simp only [CollatzResearch.WordTrace]
  refine ⟨55283214798772813497173917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73710953065030417996231889 55283214798772813497173917)
  ·
    refine ⟨20731205549539805061440219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55283214798772813497173917 20731205549539805061440219)
    ·
      refine ⟨31096808324309707592160329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20731205549539805061440219 31096808324309707592160329)
      ·
        refine ⟨23322606243232280694120247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31096808324309707592160329 23322606243232280694120247)
        ·
          refine ⟨34983909364848421041180371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23322606243232280694120247 34983909364848421041180371)
          ·
            refine ⟨52475864047272631561770557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34983909364848421041180371 52475864047272631561770557)
            ·
              refine ⟨19678449017727236835663959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52475864047272631561770557 19678449017727236835663959)
              ·
                refine ⟨29517673526590855253495939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19678449017727236835663959 29517673526590855253495939)
                ·
                  refine ⟨44276510289886282880243909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29517673526590855253495939 44276510289886282880243909)
                  ·
                    refine ⟨8301845679353678040045733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 44276510289886282880243909 8301845679353678040045733)
                    ·
                      refine ⟨1556596064878814632508575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8301845679353678040045733 1556596064878814632508575)
                      ·
                        rfl

theorem cell23_3031460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 3, 1, 1, 4, 4].length) (baseStart_3031460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3031460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3031460 prefixEnd_3031460 := by exact prefixLift 3031460
  have htrace : WordTrace (prefixWord ++ tailWord_3031460) baseStart_3031460 baseEnd_3031460 := by
    simpa [prefixWord, tailWord_3031460, baseEnd_3031460] using wordTrace_append hprefix tailTrace_3031460
  have hstable : (prefixWord ++ tailWord_3031460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3031460).length < 2 ^ (prefixWord ++ tailWord_3031460).sum := by decide
  have hdescent : baseEnd_3031460 < baseStart_3031460 := by decide
  rcases family_descends (prefixWord ++ tailWord_3031460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3031480 : List Nat := [2, 1, 2, 1, 2, 2, 1, 1, 3, 5, 3]
def baseStart_3031480 : Nat := 118140960795 + 3031480 * 2 ^ 59
def prefixEnd_3031480 : Nat := 4983230072969 + 3 ^ 40 * 3031480 * 2
def baseEnd_3031480 : Nat := 1556606334491904554258483

theorem tailTrace_3031480 : CollatzResearch.WordTrace tailWord_3031480 prefixEnd_3031480 1556606334491904554258483 := by
  unfold tailWord_3031480
  simp only [CollatzResearch.WordTrace]
  refine ⟨55283579528736585205037947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73711439371648780273383929 55283579528736585205037947)
  ·
    refine ⟨82925369293104877807556921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55283579528736585205037947 82925369293104877807556921)
    ·
      refine ⟨62194026969828658355667691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82925369293104877807556921 62194026969828658355667691)
      ·
        refine ⟨93291040454742987533501537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62194026969828658355667691 93291040454742987533501537)
        ·
          refine ⟨69968280341057240650126153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93291040454742987533501537 69968280341057240650126153)
          ·
            refine ⟨52476210255792930487594615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69968280341057240650126153 52476210255792930487594615)
            ·
              refine ⟨78714315383689395731391923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52476210255792930487594615 78714315383689395731391923)
              ·
                refine ⟨118071473075534093597087885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 78714315383689395731391923 118071473075534093597087885)
                ·
                  refine ⟨44276802403325285098907957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 118071473075534093597087885 44276802403325285098907957)
                  ·
                    refine ⟨4150950225311745478022621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 44276802403325285098907957 4150950225311745478022621)
                    ·
                      refine ⟨1556606334491904554258483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4150950225311745478022621 1556606334491904554258483)
                      ·
                        rfl

theorem cell23_3031480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 1, 3, 5, 3].length) (baseStart_3031480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3031480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3031480 prefixEnd_3031480 := by exact prefixLift 3031480
  have htrace : WordTrace (prefixWord ++ tailWord_3031480) baseStart_3031480 baseEnd_3031480 := by
    simpa [prefixWord, tailWord_3031480, baseEnd_3031480] using wordTrace_append hprefix tailTrace_3031480
  have hstable : (prefixWord ++ tailWord_3031480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3031480).length < 2 ^ (prefixWord ++ tailWord_3031480).sum := by decide
  have hdescent : baseEnd_3031480 < baseStart_3031480 := by decide
  rcases family_descends (prefixWord ++ tailWord_3031480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3031520 : List Nat := [2, 1, 1, 3, 1, 1, 3, 1, 3, 3, 4]
def baseStart_3031520 : Nat := 118140960795 + 3031520 * 2 ^ 59
def prefixEnd_3031520 : Nat := 4983230072969 + 3 ^ 40 * 3031520 * 2
def baseEnd_3031520 : Nat := 1556626873718084397758299

theorem tailTrace_3031520 : CollatzResearch.WordTrace tailWord_3031520 prefixEnd_3031520 1556626873718084397758299 := by
  unfold tailWord_3031520
  simp only [CollatzResearch.WordTrace]
  refine ⟨55284308988664128620766007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73712411984885504827688009 55284308988664128620766007)
  ·
    refine ⟨82926463482996192931149011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55284308988664128620766007 82926463482996192931149011)
    ·
      refine ⟨124389695224494289396723517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82926463482996192931149011 124389695224494289396723517)
      ·
        refine ⟨46646135709185358523771319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 124389695224494289396723517 46646135709185358523771319)
        ·
          refine ⟨69969203563778037785656979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46646135709185358523771319 69969203563778037785656979)
          ·
            refine ⟨104953805345667056678485469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69969203563778037785656979 104953805345667056678485469)
            ·
              refine ⟨39357677004625146254432051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 104953805345667056678485469 39357677004625146254432051)
              ·
                refine ⟨59036515506937719381648077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39357677004625146254432051 59036515506937719381648077)
                ·
                  refine ⟨22138693315101644768118029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 59036515506937719381648077 22138693315101644768118029)
                  ·
                    refine ⟨8302009993163116788044261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22138693315101644768118029 8302009993163116788044261)
                    ·
                      refine ⟨1556626873718084397758299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8302009993163116788044261 1556626873718084397758299)
                      ·
                        rfl

theorem cell23_3031520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 1, 3, 3, 4].length) (baseStart_3031520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3031520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3031520 prefixEnd_3031520 := by exact prefixLift 3031520
  have htrace : WordTrace (prefixWord ++ tailWord_3031520) baseStart_3031520 baseEnd_3031520 := by
    simpa [prefixWord, tailWord_3031520, baseEnd_3031520] using wordTrace_append hprefix tailTrace_3031520
  have hstable : (prefixWord ++ tailWord_3031520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3031520).length < 2 ^ (prefixWord ++ tailWord_3031520).sum := by decide
  have hdescent : baseEnd_3031520 < baseStart_3031520 := by decide
  rcases family_descends (prefixWord ++ tailWord_3031520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3031537 : List Nat := [1, 2, 2, 2, 3, 1, 2, 3, 2, 1, 4]
def baseStart_3031537 : Nat := 118140960795 + 3031537 * 2 ^ 59
def prefixEnd_3031537 : Nat := 4983230072969 + 3 ^ 40 * 3031537 * 2
def baseEnd_3031537 : Nat := 1556635602889210831245721

theorem tailTrace_3031537 : CollatzResearch.WordTrace tailWord_3031537 prefixEnd_3031537 1556635602889210831245721 := by
  unfold tailWord_3031537
  simp only [CollatzResearch.WordTrace]
  refine ⟨110569238018266669144900865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73712825345511112763267243 110569238018266669144900865)
  ·
    refine ⟨82926928513700001858675649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110569238018266669144900865 82926928513700001858675649)
    ·
      refine ⟨62195196385275001394006737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82926928513700001858675649 62195196385275001394006737)
      ·
        refine ⟨46646397288956251045505053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62195196385275001394006737 46646397288956251045505053)
        ·
          refine ⟨17492398983358594142064395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46646397288956251045505053 17492398983358594142064395)
          ·
            refine ⟨26238598475037891213096593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17492398983358594142064395 26238598475037891213096593)
            ·
              refine ⟨19678948856278418409822445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26238598475037891213096593 19678948856278418409822445)
              ·
                refine ⟨7379605821104406903683417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19678948856278418409822445 7379605821104406903683417)
                ·
                  refine ⟨5534704365828305177762563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7379605821104406903683417 5534704365828305177762563)
                  ·
                    refine ⟨8302056548742457766643845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5534704365828305177762563 8302056548742457766643845)
                    ·
                      refine ⟨1556635602889210831245721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8302056548742457766643845 1556635602889210831245721)
                      ·
                        rfl

theorem cell23_3031537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 2, 3, 2, 1, 4].length) (baseStart_3031537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3031537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3031537 prefixEnd_3031537 := by exact prefixLift 3031537
  have htrace : WordTrace (prefixWord ++ tailWord_3031537) baseStart_3031537 baseEnd_3031537 := by
    simpa [prefixWord, tailWord_3031537, baseEnd_3031537] using wordTrace_append hprefix tailTrace_3031537
  have hstable : (prefixWord ++ tailWord_3031537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3031537).length < 2 ^ (prefixWord ++ tailWord_3031537).sum := by decide
  have hdescent : baseEnd_3031537 < baseStart_3031537 := by decide
  rcases family_descends (prefixWord ++ tailWord_3031537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3031538 : List Nat := [3, 2, 1, 4, 3, 1, 1, 3, 5]
def baseStart_3031538 : Nat := 118140960795 + 3031538 * 2 ^ 59
def prefixEnd_3031538 : Nat := 4983230072969 + 3 ^ 40 * 3031538 * 2
def baseEnd_3031538 : Nat := 172959568485540591925913

theorem tailTrace_3031538 : CollatzResearch.WordTrace tailWord_3031538 prefixEnd_3031538 172959568485540591925913 := by
  unfold tailWord_3031538
  simp only [CollatzResearch.WordTrace]
  refine ⟨27642318622815761578921817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73712849660842030877124845 27642318622815761578921817)
  ·
    refine ⟨20731738967111821184191363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27642318622815761578921817 20731738967111821184191363)
    ·
      refine ⟨31097608450667731776287045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20731738967111821184191363 31097608450667731776287045)
      ·
        refine ⟨5830801584500199708053821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31097608450667731776287045 5830801584500199708053821)
        ·
          refine ⟨2186550594187574890520183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5830801584500199708053821 2186550594187574890520183)
          ·
            refine ⟨3279825891281362335780275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2186550594187574890520183 3279825891281362335780275)
            ·
              refine ⟨4919738836922043503670413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3279825891281362335780275 4919738836922043503670413)
              ·
                refine ⟨1844902063845766313876405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4919738836922043503670413 1844902063845766313876405)
                ·
                  refine ⟨172959568485540591925913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1844902063845766313876405 172959568485540591925913)
                  ·
                    rfl

theorem cell23_3031538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 3, 1, 1, 3, 5].length) (baseStart_3031538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3031538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3031538 prefixEnd_3031538 := by exact prefixLift 3031538
  have htrace : WordTrace (prefixWord ++ tailWord_3031538) baseStart_3031538 baseEnd_3031538 := by
    simpa [prefixWord, tailWord_3031538, baseEnd_3031538] using wordTrace_append hprefix tailTrace_3031538
  have hstable : (prefixWord ++ tailWord_3031538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3031538).length < 2 ^ (prefixWord ++ tailWord_3031538).sum := by decide
  have hdescent : baseEnd_3031538 < baseStart_3031538 := by decide
  rcases family_descends (prefixWord ++ tailWord_3031538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3031557 : List Nat := [1, 3, 1, 1, 2, 2, 3, 1, 4, 2, 3]
def baseStart_3031557 : Nat := 118140960795 + 3031557 * 2 ^ 59
def prefixEnd_3031557 : Nat := 4983230072969 + 3 ^ 40 * 3031557 * 2
def baseEnd_3031557 : Nat := 1556645872502300752995629

theorem tailTrace_3031557 : CollatzResearch.WordTrace tailWord_3031557 prefixEnd_3031557 1556645872502300752995629 := by
  unfold tailWord_3031557
  simp only [CollatzResearch.WordTrace]
  refine ⟨110569967478194212560628925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73713311652129475040419283 110569967478194212560628925)
  ·
    refine ⟨41463737804322829710235847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 110569967478194212560628925 41463737804322829710235847)
    ·
      refine ⟨62195606706484244565353771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41463737804322829710235847 62195606706484244565353771)
      ·
        refine ⟨93293410059726366848030657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62195606706484244565353771 93293410059726366848030657)
        ·
          refine ⟨69970057544794775136022993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93293410059726366848030657 69970057544794775136022993)
          ·
            refine ⟨52477543158596081352017245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69970057544794775136022993 52477543158596081352017245)
            ·
              refine ⟨19679078684473530507006467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52477543158596081352017245 19679078684473530507006467)
              ·
                refine ⟨29518618026710295760509701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19679078684473530507006467 29518618026710295760509701)
                ·
                  refine ⟨5534740880008180455095569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29518618026710295760509701 5534740880008180455095569)
                  ·
                    refine ⟨4151055660006135341321677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5534740880008180455095569 4151055660006135341321677)
                    ·
                      refine ⟨1556645872502300752995629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4151055660006135341321677 1556645872502300752995629)
                      ·
                        rfl

theorem cell23_3031557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 3, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 3, 1, 4, 2, 3].length) (baseStart_3031557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3031557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3031557 prefixEnd_3031557 := by exact prefixLift 3031557
  have htrace : WordTrace (prefixWord ++ tailWord_3031557) baseStart_3031557 baseEnd_3031557 := by
    simpa [prefixWord, tailWord_3031557, baseEnd_3031557] using wordTrace_append hprefix tailTrace_3031557
  have hstable : (prefixWord ++ tailWord_3031557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3031557).length < 2 ^ (prefixWord ++ tailWord_3031557).sum := by decide
  have hdescent : baseEnd_3031557 < baseStart_3031557 := by decide
  rcases family_descends (prefixWord ++ tailWord_3031557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3031564 : List Nat := [2, 2, 1, 2, 4, 1, 3, 1, 3, 4]
def baseStart_3031564 : Nat := 118140960795 + 3031564 * 2 ^ 59
def prefixEnd_3031564 : Nat := 4983230072969 + 3 ^ 40 * 3031564 * 2
def baseEnd_3031564 : Nat := 518883155622294075202699

theorem tailTrace_3031564 : CollatzResearch.WordTrace tailWord_3031564 prefixEnd_3031564 518883155622294075202699 := by
  unfold tailWord_3031564
  simp only [CollatzResearch.WordTrace]
  refine ⟨55285111394584426378066873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73713481859445901837422497 55285111394584426378066873)
  ·
    refine ⟨41463833545938319783550155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55285111394584426378066873 41463833545938319783550155)
    ·
      refine ⟨62195750318907479675325233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41463833545938319783550155 62195750318907479675325233)
      ·
        refine ⟨46646812739180609756493925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62195750318907479675325233 46646812739180609756493925)
        ·
          refine ⟨8746277388596364329342611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 46646812739180609756493925 8746277388596364329342611)
          ·
            refine ⟨13119416082894546494013917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8746277388596364329342611 13119416082894546494013917)
            ·
              refine ⟨4919781031085454935255219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13119416082894546494013917 4919781031085454935255219)
              ·
                refine ⟨7379671546628182402882829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4919781031085454935255219 7379671546628182402882829)
                ·
                  refine ⟨2767376829985568401081061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7379671546628182402882829 2767376829985568401081061)
                  ·
                    refine ⟨518883155622294075202699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2767376829985568401081061 518883155622294075202699)
                    ·
                      rfl

theorem cell23_3031564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 3, 1, 3, 4].length) (baseStart_3031564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3031564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3031564 prefixEnd_3031564 := by exact prefixLift 3031564
  have htrace : WordTrace (prefixWord ++ tailWord_3031564) baseStart_3031564 baseEnd_3031564 := by
    simpa [prefixWord, tailWord_3031564, baseEnd_3031564] using wordTrace_append hprefix tailTrace_3031564
  have hstable : (prefixWord ++ tailWord_3031564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3031564).length < 2 ^ (prefixWord ++ tailWord_3031564).sum := by decide
  have hdescent : baseEnd_3031564 < baseStart_3031564 := by decide
  rcases family_descends (prefixWord ++ tailWord_3031564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3031627 : List Nat := [1, 1, 1, 1, 3, 1, 5, 2, 3, 1, 4]
def baseStart_3031627 : Nat := 118140960795 + 3031627 * 2 ^ 59
def prefixEnd_3031627 : Nat := 4983230072969 + 3 ^ 40 * 3031627 * 2
def baseEnd_3031627 : Nat := 1556681816148115479120307

theorem tailTrace_3031627 : CollatzResearch.WordTrace tailWord_3031627 prefixEnd_3031627 1556681816148115479120307 := by
  unfold tailWord_3031627
  simp only [CollatzResearch.WordTrace]
  refine ⟨110572520587940614515677135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73715013725293743010451423 110572520587940614515677135)
  ·
    refine ⟨165858780881910921773515703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110572520587940614515677135 165858780881910921773515703)
    ·
      refine ⟨248788171322866382660273555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165858780881910921773515703 248788171322866382660273555)
      ·
        refine ⟨373182256984299573990410333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 248788171322866382660273555 373182256984299573990410333)
        ·
          refine ⟨139943346369112340246403875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 373182256984299573990410333 139943346369112340246403875)
          ·
            refine ⟨209915019553668510369605813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 139943346369112340246403875 209915019553668510369605813)
            ·
              refine ⟨19679533083156422847150545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 209915019553668510369605813 19679533083156422847150545)
              ·
                refine ⟨14759649812367317135362909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19679533083156422847150545 14759649812367317135362909)
                ·
                  refine ⟨5534868679637743925761091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14759649812367317135362909 5534868679637743925761091)
                  ·
                    refine ⟨8302303019456615888641637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5534868679637743925761091 8302303019456615888641637)
                    ·
                      refine ⟨1556681816148115479120307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8302303019456615888641637 1556681816148115479120307)
                      ·
                        rfl

theorem cell23_3031627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 5, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 5, 2, 3, 1, 4].length) (baseStart_3031627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3031627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3031627 prefixEnd_3031627 := by exact prefixLift 3031627
  have htrace : WordTrace (prefixWord ++ tailWord_3031627) baseStart_3031627 baseEnd_3031627 := by
    simpa [prefixWord, tailWord_3031627, baseEnd_3031627] using wordTrace_append hprefix tailTrace_3031627
  have hstable : (prefixWord ++ tailWord_3031627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3031627).length < 2 ^ (prefixWord ++ tailWord_3031627).sum := by decide
  have hdescent : baseEnd_3031627 < baseStart_3031627 := by decide
  rcases family_descends (prefixWord ++ tailWord_3031627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3031637 : List Nat := [1, 3, 2, 2, 1, 1, 3, 3, 1, 6]
def baseStart_3031637 : Nat := 118140960795 + 3031637 * 2 ^ 59
def prefixEnd_3031637 : Nat := 4983230072969 + 3 ^ 40 * 3031637 * 2
def baseEnd_3031637 : Nat := 518895650318220146665087

theorem tailTrace_3031637 : CollatzResearch.WordTrace tailWord_3031637 prefixEnd_3031637 518895650318220146665087 := by
  unfold tailWord_3031637
  simp only [CollatzResearch.WordTrace]
  refine ⟨110572885317904386223541165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73715256878602924149027443 110572885317904386223541165)
  ·
    refine ⟨41464831994214144833827937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 110572885317904386223541165 41464831994214144833827937)
    ·
      refine ⟨31098623995660608625370953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41464831994214144833827937 31098623995660608625370953)
      ·
        refine ⟨23323967996745456469028215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31098623995660608625370953 23323967996745456469028215)
        ·
          refine ⟨34985951995118184703542323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23323967996745456469028215 34985951995118184703542323)
          ·
            refine ⟨52478927992677277055313485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34985951995118184703542323 52478927992677277055313485)
            ·
              refine ⟨19679597997253978895742557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52478927992677277055313485 19679597997253978895742557)
              ·
                refine ⟨7379849248970242085903459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19679597997253978895742557 7379849248970242085903459)
                ·
                  refine ⟨11069773873455363128855189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7379849248970242085903459 11069773873455363128855189)
                  ·
                    refine ⟨518895650318220146665087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11069773873455363128855189 518895650318220146665087)
                    ·
                      rfl

theorem cell23_3031637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 3, 3, 1, 6].length) (baseStart_3031637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3031637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3031637 prefixEnd_3031637 := by exact prefixLift 3031637
  have htrace : WordTrace (prefixWord ++ tailWord_3031637) baseStart_3031637 baseEnd_3031637 := by
    simpa [prefixWord, tailWord_3031637, baseEnd_3031637] using wordTrace_append hprefix tailTrace_3031637
  have hstable : (prefixWord ++ tailWord_3031637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3031637).length < 2 ^ (prefixWord ++ tailWord_3031637).sum := by decide
  have hdescent : baseEnd_3031637 < baseStart_3031637 := by decide
  rcases family_descends (prefixWord ++ tailWord_3031637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3031661 : List Nat := [1, 5, 1, 1, 3, 2, 1, 3, 1, 1, 4]
def baseStart_3031661 : Nat := 118140960795 + 3031661 * 2 ^ 59
def prefixEnd_3031661 : Nat := 4983230072969 + 3 ^ 40 * 3031661 * 2
def baseEnd_3031661 : Nat := 1556699274490368346095151

theorem tailTrace_3031661 : CollatzResearch.WordTrace tailWord_3031661 prefixEnd_3031661 1556699274490368346095151 := by
  unfold tailWord_3031661
  simp only [CollatzResearch.WordTrace]
  refine ⟨110573760669817438322414837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73715840446544958881609891 110573760669817438322414837)
  ·
    refine ⟨10366290062795384842726391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 110573760669817438322414837 10366290062795384842726391)
    ·
      refine ⟨15549435094193077264089587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10366290062795384842726391 15549435094193077264089587)
      ·
        refine ⟨23324152641289615896134381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15549435094193077264089587 23324152641289615896134381)
        ·
          refine ⟨8746557240483605961050393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23324152641289615896134381 8746557240483605961050393)
          ·
            refine ⟨6559917930362704470787795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8746557240483605961050393 6559917930362704470787795)
            ·
              refine ⟨9839876895544056706181693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6559917930362704470787795 9839876895544056706181693)
              ·
                refine ⟨3689953835829021264818135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9839876895544056706181693 3689953835829021264818135)
                ·
                  refine ⟨5534930753743531897227203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3689953835829021264818135 5534930753743531897227203)
                  ·
                    refine ⟨8302396130615297845840805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5534930753743531897227203 8302396130615297845840805)
                    ·
                      refine ⟨1556699274490368346095151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8302396130615297845840805 1556699274490368346095151)
                      ·
                        rfl

theorem cell23_3031661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 1, 3, 1, 1, 4].length) (baseStart_3031661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3031661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3031661 prefixEnd_3031661 := by exact prefixLift 3031661
  have htrace : WordTrace (prefixWord ++ tailWord_3031661) baseStart_3031661 baseEnd_3031661 := by
    simpa [prefixWord, tailWord_3031661, baseEnd_3031661] using wordTrace_append hprefix tailTrace_3031661
  have hstable : (prefixWord ++ tailWord_3031661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3031661).length < 2 ^ (prefixWord ++ tailWord_3031661).sum := by decide
  have hdescent : baseEnd_3031661 < baseStart_3031661 := by decide
  rcases family_descends (prefixWord ++ tailWord_3031661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3031698 : List Nat := [3, 2, 3, 1, 2, 2, 2, 2, 1, 2, 3]
def baseStart_3031698 : Nat := 118140960795 + 3031698 * 2 ^ 59
def prefixEnd_3031698 : Nat := 4983230072969 + 3 ^ 40 * 3031698 * 2
def baseEnd_3031698 : Nat := 1556718273274584701332481

theorem tailTrace_3031698 : CollatzResearch.WordTrace tailWord_3031698 prefixEnd_3031698 1556718273274584701332481 := by
  unfold tailWord_3031698
  simp only [CollatzResearch.WordTrace]
  refine ⟨27643777542670848410377937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73716740113788929094341165 27643777542670848410377937)
  ·
    refine ⟨20732833157003136307783453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27643777542670848410377937 20732833157003136307783453)
    ·
      refine ⟨7774812433876176115418795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20732833157003136307783453 7774812433876176115418795)
      ·
        refine ⟨11662218650814264173128193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7774812433876176115418795 11662218650814264173128193)
        ·
          refine ⟨8746663988110698129846145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11662218650814264173128193 8746663988110698129846145)
          ·
            refine ⟨6559997991083023597384609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8746663988110698129846145 6559997991083023597384609)
            ·
              refine ⟨4919998493312267698038457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6559997991083023597384609 4919998493312267698038457)
              ·
                refine ⟨3689998869984200773528843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4919998493312267698038457 3689998869984200773528843)
                ·
                  refine ⟨5534998304976301160293265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3689998869984200773528843 5534998304976301160293265)
                  ·
                    refine ⟨4151248728732225870219949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5534998304976301160293265 4151248728732225870219949)
                    ·
                      refine ⟨1556718273274584701332481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4151248728732225870219949 1556718273274584701332481)
                      ·
                        rfl

theorem cell23_3031698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 2, 2, 1, 2, 3].length) (baseStart_3031698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3031698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3031698 prefixEnd_3031698 := by exact prefixLift 3031698
  have htrace : WordTrace (prefixWord ++ tailWord_3031698) baseStart_3031698 baseEnd_3031698 := by
    simpa [prefixWord, tailWord_3031698, baseEnd_3031698] using wordTrace_append hprefix tailTrace_3031698
  have hstable : (prefixWord ++ tailWord_3031698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3031698).length < 2 ^ (prefixWord ++ tailWord_3031698).sum := by decide
  have hdescent : baseEnd_3031698 < baseStart_3031698 := by decide
  rcases family_descends (prefixWord ++ tailWord_3031698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3031712 : List Nat := [2, 1, 1, 4, 4, 2, 1, 3, 1, 2, 2]
def baseStart_3031712 : Nat := 118140960795 + 3031712 * 2 ^ 59
def prefixEnd_3031712 : Nat := 4983230072969 + 3 ^ 40 * 3031712 * 2
def baseEnd_3031712 : Nat := 1556725462003747646557417

theorem tailTrace_3031712 : CollatzResearch.WordTrace tailWord_3031712 prefixEnd_3031712 1556725462003747646557417 := by
  unfold tailWord_3031712
  simp only [CollatzResearch.WordTrace]
  refine ⟨55287810396316337016260695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73717080528421782688347593 55287810396316337016260695)
  ·
    refine ⟨82931715594474505524391043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55287810396316337016260695 82931715594474505524391043)
    ·
      refine ⟨124397573391711758286586565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82931715594474505524391043 124397573391711758286586565)
      ·
        refine ⟨23324545010945954678734981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 124397573391711758286586565 23324545010945954678734981)
        ·
          refine ⟨4373352189552366502262809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23324545010945954678734981 4373352189552366502262809)
          ·
            refine ⟨3280014142164274876697107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4373352189552366502262809 3280014142164274876697107)
            ·
              refine ⟨4920021213246412315045661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3280014142164274876697107 4920021213246412315045661)
              ·
                refine ⟨1845007954967404618142123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4920021213246412315045661 1845007954967404618142123)
                ·
                  refine ⟨2767511932451106927213185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1845007954967404618142123 2767511932451106927213185)
                  ·
                    refine ⟨2075633949338330195409889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2767511932451106927213185 2075633949338330195409889)
                    ·
                      refine ⟨1556725462003747646557417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2075633949338330195409889 1556725462003747646557417)
                      ·
                        rfl

theorem cell23_3031712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 2, 1, 3, 1, 2, 2].length) (baseStart_3031712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3031712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3031712 prefixEnd_3031712 := by exact prefixLift 3031712
  have htrace : WordTrace (prefixWord ++ tailWord_3031712) baseStart_3031712 baseEnd_3031712 := by
    simpa [prefixWord, tailWord_3031712, baseEnd_3031712] using wordTrace_append hprefix tailTrace_3031712
  have hstable : (prefixWord ++ tailWord_3031712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3031712).length < 2 ^ (prefixWord ++ tailWord_3031712).sum := by decide
  have hdescent : baseEnd_3031712 < baseStart_3031712 := by decide
  rcases family_descends (prefixWord ++ tailWord_3031712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3031717 : List Nat := [1, 3, 1, 2, 1, 2, 1, 2, 1, 5, 4]
def baseStart_3031717 : Nat := 118140960795 + 3031717 * 2 ^ 59
def prefixEnd_3031717 : Nat := 4983230072969 + 3 ^ 40 * 3031717 * 2
def baseEnd_3031717 : Nat := 1556728029407020126994893

theorem tailTrace_3031717 : CollatzResearch.WordTrace tailWord_3031717 prefixEnd_3031717 1556728029407020126994893 := by
  unfold tailWord_3031717
  simp only [CollatzResearch.WordTrace]
  refine ⟨110575803157614559886453405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73717202105076373257635603 110575803157614559886453405)
  ·
    refine ⟨41465926184105459957420027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 110575803157614559886453405 41465926184105459957420027)
    ·
      refine ⟨62198889276158189936130041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41465926184105459957420027 62198889276158189936130041)
      ·
        refine ⟨46649166957118642452097531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62198889276158189936130041 46649166957118642452097531)
        ·
          refine ⟨69973750435677963678146297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46649166957118642452097531 69973750435677963678146297)
          ·
            refine ⟨52480312826758472758609723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69973750435677963678146297 52480312826758472758609723)
            ·
              refine ⟨78720469240137709137914585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52480312826758472758609723 78720469240137709137914585)
              ·
                refine ⟨59040351930103281853435939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 78720469240137709137914585 59040351930103281853435939)
                ·
                  refine ⟨88560527895154922780153909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 59040351930103281853435939 88560527895154922780153909)
                  ·
                    refine ⟨8302549490170774010639429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 88560527895154922780153909 8302549490170774010639429)
                    ·
                      refine ⟨1556728029407020126994893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8302549490170774010639429 1556728029407020126994893)
                      ·
                        rfl

theorem cell23_3031717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 2, 1, 5, 4].length) (baseStart_3031717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3031717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3031717 prefixEnd_3031717 := by exact prefixLift 3031717
  have htrace : WordTrace (prefixWord ++ tailWord_3031717) baseStart_3031717 baseEnd_3031717 := by
    simpa [prefixWord, tailWord_3031717, baseEnd_3031717] using wordTrace_append hprefix tailTrace_3031717
  have hstable : (prefixWord ++ tailWord_3031717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3031717).length < 2 ^ (prefixWord ++ tailWord_3031717).sum := by decide
  have hdescent : baseEnd_3031717 < baseStart_3031717 := by decide
  rcases family_descends (prefixWord ++ tailWord_3031717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3031729 : List Nat := [1, 2, 2, 6, 1, 1, 3, 2, 1, 2, 2]
def baseStart_3031729 : Nat := 118140960795 + 3031729 * 2 ^ 59
def prefixEnd_3031729 : Nat := 4983230072969 + 3 ^ 40 * 3031729 * 2
def baseEnd_3031729 : Nat := 1556734191174874080044839

theorem tailTrace_3031729 : CollatzResearch.WordTrace tailWord_3031729 prefixEnd_3031729 1556734191174874080044839 := by
  unfold tailWord_3031729
  simp only [CollatzResearch.WordTrace]
  refine ⟨110576240833571085935890241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73717493889047390623926827 110576240833571085935890241)
  ·
    refine ⟨82932180625178314451917681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110576240833571085935890241 82932180625178314451917681)
    ·
      refine ⟨62199135468883735838938261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82932180625178314451917681 62199135468883735838938261)
      ·
        refine ⟨2915584475103925117450231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 62199135468883735838938261 2915584475103925117450231)
        ·
          refine ⟨4373376712655887676175347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2915584475103925117450231 4373376712655887676175347)
          ·
            refine ⟨6560065068983831514263021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4373376712655887676175347 6560065068983831514263021)
            ·
              refine ⟨2460024400868936817848633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6560065068983831514263021 2460024400868936817848633)
              ·
                refine ⟨1845018300651702613386475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2460024400868936817848633 1845018300651702613386475)
                ·
                  refine ⟨2767527450977553920079713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1845018300651702613386475 2767527450977553920079713)
                  ·
                    refine ⟨2075645588233165440059785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2767527450977553920079713 2075645588233165440059785)
                    ·
                      refine ⟨1556734191174874080044839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2075645588233165440059785 1556734191174874080044839)
                      ·
                        rfl

theorem cell23_3031729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 3, 2, 1, 2, 2].length) (baseStart_3031729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3031729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3031729 prefixEnd_3031729 := by exact prefixLift 3031729
  have htrace : WordTrace (prefixWord ++ tailWord_3031729) baseStart_3031729 baseEnd_3031729 := by
    simpa [prefixWord, tailWord_3031729, baseEnd_3031729] using wordTrace_append hprefix tailTrace_3031729
  have hstable : (prefixWord ++ tailWord_3031729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3031729).length < 2 ^ (prefixWord ++ tailWord_3031729).sum := by decide
  have hdescent : baseEnd_3031729 < baseStart_3031729 := by decide
  rcases family_descends (prefixWord ++ tailWord_3031729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3031737 : List Nat := [1, 2, 1, 4, 1, 1, 1, 1, 3, 3, 5]
def baseStart_3031737 : Nat := 118140960795 + 3031737 * 2 ^ 59
def prefixEnd_3031737 : Nat := 4983230072969 + 3 ^ 40 * 3031737 * 2
def baseEnd_3031737 : Nat := 1556738299020110048744801

theorem tailTrace_3031737 : CollatzResearch.WordTrace tailWord_3031737 prefixEnd_3031737 1556738299020110048744801 := by
  unfold tailWord_3031737
  simp only [CollatzResearch.WordTrace]
  refine ⟨110576532617542103302181465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73717688411694735534787643 110576532617542103302181465)
  ·
    refine ⟨82932399463156577476636099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110576532617542103302181465 82932399463156577476636099)
    ·
      refine ⟨124398599194734866214954149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82932399463156577476636099 124398599194734866214954149)
      ·
        refine ⟨23324737349012787415303903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 124398599194734866214954149 23324737349012787415303903)
        ·
          refine ⟨34987106023519181122955855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23324737349012787415303903 34987106023519181122955855)
          ·
            refine ⟨52480659035278771684433783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34987106023519181122955855 52480659035278771684433783)
            ·
              refine ⟨78720988552918157526650675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52480659035278771684433783 78720988552918157526650675)
              ·
                refine ⟨118081482829377236289976013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 78720988552918157526650675 118081482829377236289976013)
                ·
                  refine ⟨44280556061016463608741005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 118081482829377236289976013 44280556061016463608741005)
                  ·
                    refine ⟨16605208522881173853277877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 44280556061016463608741005 16605208522881173853277877)
                    ·
                      refine ⟨1556738299020110048744801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16605208522881173853277877 1556738299020110048744801)
                      ·
                        rfl

theorem cell23_3031737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 1, 3, 3, 5].length) (baseStart_3031737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3031737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3031737 prefixEnd_3031737 := by exact prefixLift 3031737
  have htrace : WordTrace (prefixWord ++ tailWord_3031737) baseStart_3031737 baseEnd_3031737 := by
    simpa [prefixWord, tailWord_3031737, baseEnd_3031737] using wordTrace_append hprefix tailTrace_3031737
  have hstable : (prefixWord ++ tailWord_3031737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3031737).length < 2 ^ (prefixWord ++ tailWord_3031737).sum := by decide
  have hdescent : baseEnd_3031737 < baseStart_3031737 := by decide
  rcases family_descends (prefixWord ++ tailWord_3031737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3031751 : List Nat := [1, 1, 4, 1, 1, 1, 2, 2, 6, 2, 2]
def baseStart_3031751 : Nat := 118140960795 + 3031751 * 2 ^ 59
def prefixEnd_3031751 : Nat := 4983230072969 + 3 ^ 40 * 3031751 * 2
def baseEnd_3031751 : Nat := 1556745487749272993969737

theorem tailTrace_3031751 : CollatzResearch.WordTrace tailWord_3031751 prefixEnd_3031751 1556745487749272993969737 := by
  unfold tailWord_3031751
  simp only [CollatzResearch.WordTrace]
  refine ⟨110577043239491383693191107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73718028826327589128794071 110577043239491383693191107)
  ·
    refine ⟨165865564859237075539786661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110577043239491383693191107 165865564859237075539786661)
    ·
      refine ⟨31099793411106951663709999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 165865564859237075539786661 31099793411106951663709999)
      ·
        refine ⟨46649690116660427495564999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31099793411106951663709999 46649690116660427495564999)
        ·
          refine ⟨69974535174990641243347499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46649690116660427495564999 69974535174990641243347499)
          ·
            refine ⟨104961802762485961865021249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69974535174990641243347499 104961802762485961865021249)
            ·
              refine ⟨78721352071864471398765937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 104961802762485961865021249 78721352071864471398765937)
              ·
                refine ⟨59041014053898353549074453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 78721352071864471398765937 59041014053898353549074453)
                ·
                  refine ⟨2767547533776485322612865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 59041014053898353549074453 2767547533776485322612865)
                  ·
                    refine ⟨2075660650332363991959649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2767547533776485322612865 2075660650332363991959649)
                    ·
                      refine ⟨1556745487749272993969737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2075660650332363991959649 1556745487749272993969737)
                      ·
                        rfl

theorem cell23_3031751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 2, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 2, 6, 2, 2].length) (baseStart_3031751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3031751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3031751 prefixEnd_3031751 := by exact prefixLift 3031751
  have htrace : WordTrace (prefixWord ++ tailWord_3031751) baseStart_3031751 baseEnd_3031751 := by
    simpa [prefixWord, tailWord_3031751, baseEnd_3031751] using wordTrace_append hprefix tailTrace_3031751
  have hstable : (prefixWord ++ tailWord_3031751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3031751).length < 2 ^ (prefixWord ++ tailWord_3031751).sum := by decide
  have hdescent : baseEnd_3031751 < baseStart_3031751 := by decide
  rcases family_descends (prefixWord ++ tailWord_3031751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3031754 : List Nat := [3, 1, 2, 1, 4, 1, 1, 2, 2, 1, 5]
def baseStart_3031754 : Nat := 118140960795 + 3031754 * 2 ^ 59
def prefixEnd_3031754 : Nat := 4983230072969 + 3 ^ 40 * 3031754 * 2
def baseEnd_3031754 : Nat := 1556747028191236482232223

theorem tailTrace_3031754 : CollatzResearch.WordTrace tailWord_3031754 prefixEnd_3031754 1556747028191236482232223 := by
  unfold tailWord_3031754
  simp only [CollatzResearch.WordTrace]
  refine ⟨27644288164620128801387579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73718101772320343470366877 27644288164620128801387579)
  ·
    refine ⟨41466432246930193202081369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27644288164620128801387579 41466432246930193202081369)
    ·
      refine ⟨31099824185197644901561027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41466432246930193202081369 31099824185197644901561027)
      ·
        refine ⟨46649736277796467352341541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31099824185197644901561027 46649736277796467352341541)
        ·
          refine ⟨8746825552086837628564039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 46649736277796467352341541 8746825552086837628564039)
          ·
            refine ⟨13120238328130256442846059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8746825552086837628564039 13120238328130256442846059)
            ·
              refine ⟨19680357492195384664269089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13120238328130256442846059 19680357492195384664269089)
              ·
                refine ⟨14760268119146538498201817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19680357492195384664269089 14760268119146538498201817)
                ·
                  refine ⟨11070201089359903873651363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14760268119146538498201817 11070201089359903873651363)
                  ·
                    refine ⟨16605301634039855810477045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11070201089359903873651363 16605301634039855810477045)
                    ·
                      refine ⟨1556747028191236482232223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16605301634039855810477045 1556747028191236482232223)
                      ·
                        rfl

theorem cell23_3031754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 1, 2, 2, 1, 5].length) (baseStart_3031754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3031754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3031754 prefixEnd_3031754 := by exact prefixLift 3031754
  have htrace : WordTrace (prefixWord ++ tailWord_3031754) baseStart_3031754 baseEnd_3031754 := by
    simpa [prefixWord, tailWord_3031754, baseEnd_3031754] using wordTrace_append hprefix tailTrace_3031754
  have hstable : (prefixWord ++ tailWord_3031754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3031754).length < 2 ^ (prefixWord ++ tailWord_3031754).sum := by decide
  have hdescent : baseEnd_3031754 < baseStart_3031754 := by decide
  rcases family_descends (prefixWord ++ tailWord_3031754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3031772 : List Nat := [2, 2, 5, 1, 1, 2, 3, 1, 1, 3, 2]
def baseStart_3031772 : Nat := 118140960795 + 3031772 * 2 ^ 59
def prefixEnd_3031772 : Nat := 4983230072969 + 3 ^ 40 * 3031772 * 2
def baseEnd_3031772 : Nat := 1556756270843017411807141

theorem tailTrace_3031772 : CollatzResearch.WordTrace tailWord_3031772 prefixEnd_3031772 1556756270843017411807141 := by
  unfold tailWord_3031772
  simp only [CollatzResearch.WordTrace]
  refine ⟨55288904586207652139852785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73718539448276869519803713 55288904586207652139852785)
  ·
    refine ⟨41466678439655739104889589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55288904586207652139852785 41466678439655739104889589)
    ·
      refine ⟨3887501103717725541083399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 41466678439655739104889589 3887501103717725541083399)
      ·
        refine ⟨5831251655576588311625099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3887501103717725541083399 5831251655576588311625099)
        ·
          refine ⟨8746877483364882467437649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5831251655576588311625099 8746877483364882467437649)
          ·
            refine ⟨6560158112523661850578237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8746877483364882467437649 6560158112523661850578237)
            ·
              refine ⟨2460059292196373193966839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6560158112523661850578237 2460059292196373193966839)
              ·
                refine ⟨3690088938294559790950259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2460059292196373193966839 3690088938294559790950259)
                ·
                  refine ⟨5535133407441839686425389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3690088938294559790950259 5535133407441839686425389)
                  ·
                    refine ⟨2075675027790689882409521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5535133407441839686425389 2075675027790689882409521)
                    ·
                      refine ⟨1556756270843017411807141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2075675027790689882409521 1556756270843017411807141)
                      ·
                        rfl

theorem cell23_3031772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 3, 1, 1, 3, 2].length) (baseStart_3031772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3031772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3031772 prefixEnd_3031772 := by exact prefixLift 3031772
  have htrace : WordTrace (prefixWord ++ tailWord_3031772) baseStart_3031772 baseEnd_3031772 := by
    simpa [prefixWord, tailWord_3031772, baseEnd_3031772] using wordTrace_append hprefix tailTrace_3031772
  have hstable : (prefixWord ++ tailWord_3031772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3031772).length < 2 ^ (prefixWord ++ tailWord_3031772).sum := by decide
  have hdescent : baseEnd_3031772 < baseStart_3031772 := by decide
  rcases family_descends (prefixWord ++ tailWord_3031772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3031787 : List Nat := [1, 1, 1, 1, 2, 4, 1, 2, 3, 7]
def baseStart_3031787 : Nat := 118140960795 + 3031787 * 2 ^ 59
def prefixEnd_3031787 : Nat := 4983230072969 + 3 ^ 40 * 3031787 * 2
def baseEnd_3031787 : Nat := 518921324350944951039857

theorem tailTrace_3031787 : CollatzResearch.WordTrace tailWord_3031787 prefixEnd_3031787 518921324350944951039857 := by
  unfold tailWord_3031787
  simp only [CollatzResearch.WordTrace]
  refine ⟨110578356267360961841501615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73718904178240641227667743 110578356267360961841501615)
  ·
    refine ⟨165867534401041442762252423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110578356267360961841501615 165867534401041442762252423)
    ·
      refine ⟨248801301601562164143378635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165867534401041442762252423 248801301601562164143378635)
      ·
        refine ⟨373201952402343246215067953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 248801301601562164143378635 373201952402343246215067953)
        ·
          refine ⟨279901464301757434661300965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 373201952402343246215067953 279901464301757434661300965)
          ·
            refine ⟨52481524556579518998993931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 279901464301757434661300965 52481524556579518998993931)
            ·
              refine ⟨78722286834869278498490897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52481524556579518998993931 78722286834869278498490897)
              ·
                refine ⟨59041715126151958873868173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 78722286834869278498490897 59041715126151958873868173)
                ·
                  refine ⟨22140643172306984577700565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 59041715126151958873868173 22140643172306984577700565)
                  ·
                    refine ⟨518921324350944951039857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 22140643172306984577700565 518921324350944951039857)
                    ·
                      rfl

theorem cell23_3031787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 2, 3, 7].length) (baseStart_3031787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3031787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3031787 prefixEnd_3031787 := by exact prefixLift 3031787
  have htrace : WordTrace (prefixWord ++ tailWord_3031787) baseStart_3031787 baseEnd_3031787 := by
    simpa [prefixWord, tailWord_3031787, baseEnd_3031787] using wordTrace_append hprefix tailTrace_3031787
  have hstable : (prefixWord ++ tailWord_3031787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3031787).length < 2 ^ (prefixWord ++ tailWord_3031787).sum := by decide
  have hdescent : baseEnd_3031787 < baseStart_3031787 := by decide
  rcases family_descends (prefixWord ++ tailWord_3031787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3031791 : List Nat := [1, 1, 2, 1, 5, 3, 1, 4, 5]
def baseStart_3031791 : Nat := 118140960795 + 3031791 * 2 ^ 59
def prefixEnd_3031791 : Nat := 4983230072969 + 3 ^ 40 * 3031791 * 2
def baseEnd_3031791 : Nat := 172974002997272537496617

theorem tailTrace_3031791 : CollatzResearch.WordTrace tailWord_3031791 prefixEnd_3031791 172974002997272537496617 := by
  unfold tailWord_3031791
  simp only [CollatzResearch.WordTrace]
  refine ⟨110578502159346470524647227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73719001439564313683098151 110578502159346470524647227)
  ·
    refine ⟨165867753239019705786970841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110578502159346470524647227 165867753239019705786970841)
    ·
      refine ⟨124400814929264779340228131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 165867753239019705786970841 124400814929264779340228131)
      ·
        refine ⟨186601222393897169010342197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124400814929264779340228131 186601222393897169010342197)
        ·
          refine ⟨17493864599427859594719581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 186601222393897169010342197 17493864599427859594719581)
          ·
            refine ⟨6560199224785447348019843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17493864599427859594719581 6560199224785447348019843)
            ·
              refine ⟨9840298837178171022029765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6560199224785447348019843 9840298837178171022029765)
              ·
                refine ⟨1845056031970907066630581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9840298837178171022029765 1845056031970907066630581)
                ·
                  refine ⟨172974002997272537496617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1845056031970907066630581 172974002997272537496617)
                  ·
                    rfl

theorem cell23_3031791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 1, 4, 5].length) (baseStart_3031791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3031791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3031791 prefixEnd_3031791 := by exact prefixLift 3031791
  have htrace : WordTrace (prefixWord ++ tailWord_3031791) baseStart_3031791 baseEnd_3031791 := by
    simpa [prefixWord, tailWord_3031791, baseEnd_3031791] using wordTrace_append hprefix tailTrace_3031791
  have hstable : (prefixWord ++ tailWord_3031791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3031791).length < 2 ^ (prefixWord ++ tailWord_3031791).sum := by decide
  have hdescent : baseEnd_3031791 < baseStart_3031791 := by decide
  rcases family_descends (prefixWord ++ tailWord_3031791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3031841 : List Nat := [1, 2, 3, 2, 1, 2, 1, 1, 4, 4, 2]
def baseStart_3031841 : Nat := 118140960795 + 3031841 * 2 ^ 59
def prefixEnd_3031841 : Nat := 4983230072969 + 3 ^ 40 * 3031841 * 2
def baseEnd_3031841 : Nat := 1556791701008177641844323

theorem tailTrace_3031841 : CollatzResearch.WordTrace tailWord_3031841 prefixEnd_3031841 1556791701008177641844323 := by
  unfold tailWord_3031841
  simp only [CollatzResearch.WordTrace]
  refine ⟨110580325809165329063967377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73720217206110219375978251 110580325809165329063967377)
  ·
    refine ⟨82935244356873996797975533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110580325809165329063967377 82935244356873996797975533)
    ·
      refine ⟨31100716633827748799240825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82935244356873996797975533 31100716633827748799240825)
      ·
        refine ⟨23325537475370811599430619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31100716633827748799240825 23325537475370811599430619)
        ·
          refine ⟨34988306213056217399145929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23325537475370811599430619 34988306213056217399145929)
          ·
            refine ⟨26241229659792163049359447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34988306213056217399145929 26241229659792163049359447)
            ·
              refine ⟨39361844489688244574039171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26241229659792163049359447 39361844489688244574039171)
              ·
                refine ⟨59042766734532366861058757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39361844489688244574039171 59042766734532366861058757)
                ·
                  refine ⟨11070518762724818786448517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 59042766734532366861058757 11070518762724818786448517)
                  ·
                    refine ⟨2075722268010903522459097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11070518762724818786448517 2075722268010903522459097)
                    ·
                      refine ⟨1556791701008177641844323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2075722268010903522459097 1556791701008177641844323)
                      ·
                        rfl

theorem cell23_3031841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 1, 4, 4, 2].length) (baseStart_3031841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3031841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3031841 prefixEnd_3031841 := by exact prefixLift 3031841
  have htrace : WordTrace (prefixWord ++ tailWord_3031841) baseStart_3031841 baseEnd_3031841 := by
    simpa [prefixWord, tailWord_3031841, baseEnd_3031841] using wordTrace_append hprefix tailTrace_3031841
  have hstable : (prefixWord ++ tailWord_3031841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3031841).length < 2 ^ (prefixWord ++ tailWord_3031841).sum := by decide
  have hdescent : baseEnd_3031841 < baseStart_3031841 := by decide
  rcases family_descends (prefixWord ++ tailWord_3031841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3031861 : List Nat := [1, 3, 3, 1, 3, 1, 1, 2, 1, 4, 3]
def baseStart_3031861 : Nat := 118140960795 + 3031861 * 2 ^ 59
def prefixEnd_3031861 : Nat := 4983230072969 + 3 ^ 40 * 3031861 * 2
def baseEnd_3031861 : Nat := 1556801970621267563594231

theorem tailTrace_3031861 : CollatzResearch.WordTrace tailWord_3031861 prefixEnd_3031861 1556801970621267563594231 := by
  unfold tailWord_3031861
  simp only [CollatzResearch.WordTrace]
  refine ⟨110581055269092872479695437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73720703512728581653130291 110581055269092872479695437)
  ·
    refine ⟨41467895725909827179885789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 110581055269092872479695437 41467895725909827179885789)
    ·
      refine ⟨15550460897216185192457171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41467895725909827179885789 15550460897216185192457171)
      ·
        refine ⟨23325691345824277788685757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15550460897216185192457171 23325691345824277788685757)
        ·
          refine ⟨8747134254684104170757159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23325691345824277788685757 8747134254684104170757159)
          ·
            refine ⟨13120701382026156256135739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8747134254684104170757159 13120701382026156256135739)
            ·
              refine ⟨19681052073039234384203609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13120701382026156256135739 19681052073039234384203609)
              ·
                refine ⟨14760789054779425788152707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19681052073039234384203609 14760789054779425788152707)
                ·
                  refine ⟨22141183582169138682229061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14760789054779425788152707 22141183582169138682229061)
                  ·
                    refine ⟨4151471921656713502917949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22141183582169138682229061 4151471921656713502917949)
                    ·
                      refine ⟨1556801970621267563594231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4151471921656713502917949 1556801970621267563594231)
                      ·
                        rfl

theorem cell23_3031861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 1, 2, 1, 4, 3].length) (baseStart_3031861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3031861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3031861 prefixEnd_3031861 := by exact prefixLift 3031861
  have htrace : WordTrace (prefixWord ++ tailWord_3031861) baseStart_3031861 baseEnd_3031861 := by
    simpa [prefixWord, tailWord_3031861, baseEnd_3031861] using wordTrace_append hprefix tailTrace_3031861
  have hstable : (prefixWord ++ tailWord_3031861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3031861).length < 2 ^ (prefixWord ++ tailWord_3031861).sum := by decide
  have hdescent : baseEnd_3031861 < baseStart_3031861 := by decide
  rcases family_descends (prefixWord ++ tailWord_3031861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3031891 : List Nat := [1, 1, 1, 2, 1, 1, 3, 4, 5, 1, 3]
def baseStart_3031891 : Nat := 118140960795 + 3031891 * 2 ^ 59
def prefixEnd_3031891 : Nat := 4983230072969 + 3 ^ 40 * 3031891 * 2
def baseEnd_3031891 : Nat := 1556817375040902446219093

theorem tailTrace_3031891 : CollatzResearch.WordTrace tailWord_3031891 prefixEnd_3031891 1556817375040902446219093 := by
  unfold tailWord_3031891
  simp only [CollatzResearch.WordTrace]
  refine ⟨110582149458984187603287527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73721432972656125068858351 110582149458984187603287527)
  ·
    refine ⟨165873224188476281404931291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110582149458984187603287527 165873224188476281404931291)
    ·
      refine ⟨248809836282714422107396937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165873224188476281404931291 248809836282714422107396937)
      ·
        refine ⟨186607377212035816580547703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 248809836282714422107396937 186607377212035816580547703)
        ·
          refine ⟨279911065818053724870821555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 186607377212035816580547703 279911065818053724870821555)
          ·
            refine ⟨419866598727080587306232333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 279911065818053724870821555 419866598727080587306232333)
            ·
              refine ⟨157449974522655220239837125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 419866598727080587306232333 157449974522655220239837125)
              ·
                refine ⟨29521870222997853794969461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 157449974522655220239837125 29521870222997853794969461)
                ·
                  refine ⟨2767675333406048793278387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 29521870222997853794969461 2767675333406048793278387)
                  ·
                    refine ⟨4151513000109073189917581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2767675333406048793278387 4151513000109073189917581)
                    ·
                      refine ⟨1556817375040902446219093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4151513000109073189917581 1556817375040902446219093)
                      ·
                        rfl

theorem cell23_3031891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 4, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 4, 5, 1, 3].length) (baseStart_3031891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3031891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3031891 prefixEnd_3031891 := by exact prefixLift 3031891
  have htrace : WordTrace (prefixWord ++ tailWord_3031891) baseStart_3031891 baseEnd_3031891 := by
    simpa [prefixWord, tailWord_3031891, baseEnd_3031891] using wordTrace_append hprefix tailTrace_3031891
  have hstable : (prefixWord ++ tailWord_3031891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3031891).length < 2 ^ (prefixWord ++ tailWord_3031891).sum := by decide
  have hdescent : baseEnd_3031891 < baseStart_3031891 := by decide
  rcases family_descends (prefixWord ++ tailWord_3031891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3031931 : List Nat := [1, 1, 1, 1, 1, 5, 2, 1, 2, 6, 2]
def baseStart_3031931 : Nat := 118140960795 + 3031931 * 2 ^ 59
def prefixEnd_3031931 : Nat := 4983230072969 + 3 ^ 40 * 3031931 * 2
def baseEnd_3031931 : Nat := 1556837914267082289718909

theorem tailTrace_3031931 : CollatzResearch.WordTrace tailWord_3031931 prefixEnd_3031931 1556837914267082289718909 := by
  unfold tailWord_3031931
  simp only [CollatzResearch.WordTrace]
  refine ⟨110583608378839274434743647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73722405585892849623162431 110583608378839274434743647)
  ·
    refine ⟨165875412568258911652115471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110583608378839274434743647 165875412568258911652115471)
    ·
      refine ⟨248813118852388367478173207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165875412568258911652115471 248813118852388367478173207)
      ·
        refine ⟨373219678278582551217259811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 248813118852388367478173207 373219678278582551217259811)
        ·
          refine ⟨559829517417873826825889717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 373219678278582551217259811 559829517417873826825889717)
          ·
            refine ⟨52484017257925671264927161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 559829517417873826825889717 52484017257925671264927161)
            ·
              refine ⟨39363012943444253448695371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52484017257925671264927161 39363012943444253448695371)
              ·
                refine ⟨59044519415166380173043057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39363012943444253448695371 59044519415166380173043057)
                ·
                  refine ⟨44283389561374785129782293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 59044519415166380173043057 44283389561374785129782293)
                  ·
                    refine ⟨2075783885689443052958545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 44283389561374785129782293 2075783885689443052958545)
                    ·
                      refine ⟨1556837914267082289718909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2075783885689443052958545 1556837914267082289718909)
                      ·
                        rfl

theorem cell23_3031931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 1, 2, 6, 2].length) (baseStart_3031931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3031931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3031931 prefixEnd_3031931 := by exact prefixLift 3031931
  have htrace : WordTrace (prefixWord ++ tailWord_3031931) baseStart_3031931 baseEnd_3031931 := by
    simpa [prefixWord, tailWord_3031931, baseEnd_3031931] using wordTrace_append hprefix tailTrace_3031931
  have hstable : (prefixWord ++ tailWord_3031931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3031931).length < 2 ^ (prefixWord ++ tailWord_3031931).sum := by decide
  have hdescent : baseEnd_3031931 < baseStart_3031931 := by decide
  rcases family_descends (prefixWord ++ tailWord_3031931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3031941 : List Nat := [1, 3, 1, 1, 3, 4, 1, 2, 1, 6]
def baseStart_3031941 : Nat := 118140960795 + 3031941 * 2 ^ 59
def prefixEnd_3031941 : Nat := 4983230072969 + 3 ^ 40 * 3031941 * 2
def baseEnd_3031941 : Nat := 518947683024542416864621

theorem tailTrace_3031941 : CollatzResearch.WordTrace tailWord_3031941 prefixEnd_3031941 518947683024542416864621 := by
  unfold tailWord_3031941
  simp only [CollatzResearch.WordTrace]
  refine ⟨110583973108803046142607677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73722648739202030761738451 110583973108803046142607677)
  ·
    refine ⟨41468989915801142303477879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 110583973108803046142607677 41468989915801142303477879)
    ·
      refine ⟨62203484873701713455216819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41468989915801142303477879 62203484873701713455216819)
      ·
        refine ⟨93305227310552570182825229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62203484873701713455216819 93305227310552570182825229)
        ·
          refine ⟨34989460241457213818559461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 93305227310552570182825229 34989460241457213818559461)
          ·
            refine ⟨6560523795273227590979899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34989460241457213818559461 6560523795273227590979899)
            ·
              refine ⟨9840785692909841386469849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6560523795273227590979899 9840785692909841386469849)
              ·
                refine ⟨7380589269682381039852387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9840785692909841386469849 7380589269682381039852387)
                ·
                  refine ⟨11070883904523571559778581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7380589269682381039852387 11070883904523571559778581)
                  ·
                    refine ⟨518947683024542416864621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11070883904523571559778581 518947683024542416864621)
                    ·
                      rfl

theorem cell23_3031941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 1, 2, 1, 6].length) (baseStart_3031941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3031941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3031941 prefixEnd_3031941 := by exact prefixLift 3031941
  have htrace : WordTrace (prefixWord ++ tailWord_3031941) baseStart_3031941 baseEnd_3031941 := by
    simpa [prefixWord, tailWord_3031941, baseEnd_3031941] using wordTrace_append hprefix tailTrace_3031941
  have hstable : (prefixWord ++ tailWord_3031941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3031941).length < 2 ^ (prefixWord ++ tailWord_3031941).sum := by decide
  have hdescent : baseEnd_3031941 < baseStart_3031941 := by decide
  rcases family_descends (prefixWord ++ tailWord_3031941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3031965 : List Nat := [1, 4, 2, 1, 2, 1, 2, 3, 3, 2, 2]
def baseStart_3031965 : Nat := 118140960795 + 3031965 * 2 ^ 59
def prefixEnd_3031965 : Nat := 4983230072969 + 3 ^ 40 * 3031965 * 2
def baseEnd_3031965 : Nat := 1556855372609335156693753

theorem tailTrace_3031965 : CollatzResearch.WordTrace tailWord_3031965 prefixEnd_3031965 1556855372609335156693753 := by
  unfold tailWord_3031965
  simp only [CollatzResearch.WordTrace]
  refine ⟨110584848460716098241481349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73723232307144065494320899 110584848460716098241481349)
  ·
    refine ⟨20734659086384268420277753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 110584848460716098241481349 20734659086384268420277753)
    ·
      refine ⟨15550994314788201315208315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20734659086384268420277753 15550994314788201315208315)
      ·
        refine ⟨23326491472182301972812473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15550994314788201315208315 23326491472182301972812473)
        ·
          refine ⟨17494868604136726479609355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23326491472182301972812473 17494868604136726479609355)
          ·
            refine ⟨26242302906205089719414033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17494868604136726479609355 26242302906205089719414033)
            ·
              refine ⟨19681727179653817289560525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26242302906205089719414033 19681727179653817289560525)
              ·
                refine ⟨7380647692370181483585197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19681727179653817289560525 7380647692370181483585197)
                ·
                  refine ⟨2767742884638818056344449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7380647692370181483585197 2767742884638818056344449)
                  ·
                    refine ⟨2075807163479113542258337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2767742884638818056344449 2075807163479113542258337)
                    ·
                      refine ⟨1556855372609335156693753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2075807163479113542258337 1556855372609335156693753)
                      ·
                        rfl

theorem cell23_3031965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 2, 3, 3, 2, 2].length) (baseStart_3031965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3031965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3031965 prefixEnd_3031965 := by exact prefixLift 3031965
  have htrace : WordTrace (prefixWord ++ tailWord_3031965) baseStart_3031965 baseEnd_3031965 := by
    simpa [prefixWord, tailWord_3031965, baseEnd_3031965] using wordTrace_append hprefix tailTrace_3031965
  have hstable : (prefixWord ++ tailWord_3031965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3031965).length < 2 ^ (prefixWord ++ tailWord_3031965).sum := by decide
  have hdescent : baseEnd_3031965 < baseStart_3031965 := by decide
  rcases family_descends (prefixWord ++ tailWord_3031965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3031998 : List Nat := [4, 2, 1, 1, 1, 2, 1, 4, 1, 3, 3]
def baseStart_3031998 : Nat := 118140960795 + 3031998 * 2 ^ 59
def prefixEnd_3031998 : Nat := 4983230072969 + 3 ^ 40 * 3031998 * 2
def baseEnd_3031998 : Nat := 1556872317470933527581101

theorem tailTrace_3031998 : CollatzResearch.WordTrace tailWord_3031998 prefixEnd_3031998 1556872317470933527581101 := by
  unfold tailWord_3031998
  simp only [CollatzResearch.WordTrace]
  refine ⟨13823256508699568109679081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 73724034713064363251621765 13823256508699568109679081)
  ·
    refine ⟨10367442381524676082259311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13823256508699568109679081 10367442381524676082259311)
    ·
      refine ⟨15551163572287014123388967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10367442381524676082259311 15551163572287014123388967)
      ·
        refine ⟨23326745358430521185083451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15551163572287014123388967 23326745358430521185083451)
        ·
          refine ⟨34990118037645781777625177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23326745358430521185083451 34990118037645781777625177)
          ·
            refine ⟨26242588528234336333218883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34990118037645781777625177 26242588528234336333218883)
            ·
              refine ⟨39363882792351504499828325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26242588528234336333218883 39363882792351504499828325)
              ·
                refine ⟨7380728023565907093717811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39363882792351504499828325 7380728023565907093717811)
                ·
                  refine ⟨11071092035348860640576717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7380728023565907093717811 11071092035348860640576717)
                  ·
                    refine ⟨4151659513255822740216269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11071092035348860640576717 4151659513255822740216269)
                    ·
                      refine ⟨1556872317470933527581101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4151659513255822740216269 1556872317470933527581101)
                      ·
                        rfl

theorem cell23_3031998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 4, 1, 3, 3].length) (baseStart_3031998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3031998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3031998 prefixEnd_3031998 := by exact prefixLift 3031998
  have htrace : WordTrace (prefixWord ++ tailWord_3031998) baseStart_3031998 baseEnd_3031998 := by
    simpa [prefixWord, tailWord_3031998, baseEnd_3031998] using wordTrace_append hprefix tailTrace_3031998
  have hstable : (prefixWord ++ tailWord_3031998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3031998).length < 2 ^ (prefixWord ++ tailWord_3031998).sum := by decide
  have hdescent : baseEnd_3031998 < baseStart_3031998 := by decide
  rcases family_descends (prefixWord ++ tailWord_3031998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3032015 : List Nat := [1, 1, 2, 1, 1, 6, 3, 2, 2, 1, 3]
def baseStart_3032015 : Nat := 118140960795 + 3032015 * 2 ^ 59
def prefixEnd_3032015 : Nat := 4983230072969 + 3 ^ 40 * 3032015 * 2
def baseEnd_3032015 : Nat := 1556881046642059961068523

theorem tailTrace_3032015 : CollatzResearch.WordTrace tailWord_3032015 prefixEnd_3032015 1556881046642059961068523 := by
  unfold tailWord_3032015
  simp only [CollatzResearch.WordTrace]
  refine ⟨110586672110534956780801499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73724448073689971187200999 110586672110534956780801499)
  ·
    refine ⟨165880008165802435171202249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110586672110534956780801499 165880008165802435171202249)
    ·
      refine ⟨124410006124351826378401687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 165880008165802435171202249 124410006124351826378401687)
      ·
        refine ⟨186615009186527739567602531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124410006124351826378401687 186615009186527739567602531)
        ·
          refine ⟨279922513779791609351403797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 186615009186527739567602531 279922513779791609351403797)
          ·
            refine ⟨13121367833427731688347053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 279922513779791609351403797 13121367833427731688347053)
            ·
              refine ⟨4920512937535399383130145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13121367833427731688347053 4920512937535399383130145)
              ·
                refine ⟨3690384703151549537347609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4920512937535399383130145 3690384703151549537347609)
                ·
                  refine ⟨2767788527363662153010707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3690384703151549537347609 2767788527363662153010707)
                  ·
                    refine ⟨4151682791045493229516061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2767788527363662153010707 4151682791045493229516061)
                    ·
                      refine ⟨1556881046642059961068523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4151682791045493229516061 1556881046642059961068523)
                      ·
                        rfl

theorem cell23_3032015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 3, 2, 2, 1, 3].length) (baseStart_3032015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3032015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3032015 prefixEnd_3032015 := by exact prefixLift 3032015
  have htrace : WordTrace (prefixWord ++ tailWord_3032015) baseStart_3032015 baseEnd_3032015 := by
    simpa [prefixWord, tailWord_3032015, baseEnd_3032015] using wordTrace_append hprefix tailTrace_3032015
  have hstable : (prefixWord ++ tailWord_3032015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3032015).length < 2 ^ (prefixWord ++ tailWord_3032015).sum := by decide
  have hdescent : baseEnd_3032015 < baseStart_3032015 := by decide
  rcases family_descends (prefixWord ++ tailWord_3032015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3032042 : List Nat := [3, 1, 3, 1, 2, 3, 2, 2, 1, 3, 2]
def baseStart_3032042 : Nat := 118140960795 + 3032042 * 2 ^ 59
def prefixEnd_3032042 : Nat := 4983230072969 + 3 ^ 40 * 3032042 * 2
def baseEnd_3032042 : Nat := 1556894910619731355430899

theorem tailTrace_3032042 : CollatzResearch.WordTrace tailWord_3032042 prefixEnd_3032042 1556894910619731355430899 := by
  unfold tailWord_3032042
  simp only [CollatzResearch.WordTrace]
  refine ⟨27646914220359285098008595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73725104587624760261356253 27646914220359285098008595)
  ·
    refine ⟨41470371330538927647012893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27646914220359285098008595 41470371330538927647012893)
    ·
      refine ⟨15551389248952097867629835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41470371330538927647012893 15551389248952097867629835)
      ·
        refine ⟨23327083873428146801444753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15551389248952097867629835 23327083873428146801444753)
        ·
          refine ⟨17495312905071110101083565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23327083873428146801444753 17495312905071110101083565)
          ·
            refine ⟨6560742339401666287906337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17495312905071110101083565 6560742339401666287906337)
            ·
              refine ⟨4920556754551249715929753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6560742339401666287906337 4920556754551249715929753)
              ·
                refine ⟨3690417565913437286947315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4920556754551249715929753 3690417565913437286947315)
                ·
                  refine ⟨5535626348870155930420973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3690417565913437286947315 5535626348870155930420973)
                  ·
                    refine ⟨2075859880826308473907865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5535626348870155930420973 2075859880826308473907865)
                    ·
                      refine ⟨1556894910619731355430899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2075859880826308473907865 1556894910619731355430899)
                      ·
                        rfl

theorem cell23_3032042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 2, 2, 1, 3, 2].length) (baseStart_3032042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3032042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3032042 prefixEnd_3032042 := by exact prefixLift 3032042
  have htrace : WordTrace (prefixWord ++ tailWord_3032042) baseStart_3032042 baseEnd_3032042 := by
    simpa [prefixWord, tailWord_3032042, baseEnd_3032042] using wordTrace_append hprefix tailTrace_3032042
  have hstable : (prefixWord ++ tailWord_3032042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3032042).length < 2 ^ (prefixWord ++ tailWord_3032042).sum := by decide
  have hdescent : baseEnd_3032042 < baseStart_3032042 := by decide
  rcases family_descends (prefixWord ++ tailWord_3032042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3032071 : List Nat := [1, 1, 4, 3, 1, 1, 1, 1, 1, 2, 7]
def baseStart_3032071 : Nat := 118140960795 + 3032071 * 2 ^ 59
def prefixEnd_3032071 : Nat := 4983230072969 + 3 ^ 40 * 3032071 * 2
def baseEnd_3032071 : Nat := 1556909801558711741968265

theorem tailTrace_3032071 : CollatzResearch.WordTrace tailWord_3032071 prefixEnd_3032071 1556909801558711741968265 := by
  unfold tailWord_3032071
  simp only [CollatzResearch.WordTrace]
  refine ⟨110588714598332078344840067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73725809732221385563226711 110588714598332078344840067)
  ·
    refine ⟨165883071897498117517260101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110588714598332078344840067 165883071897498117517260101)
    ·
      refine ⟨31103075980780897034486269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 165883071897498117517260101 31103075980780897034486269)
      ·
        refine ⟨11663653492792836387932351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31103075980780897034486269 11663653492792836387932351)
        ·
          refine ⟨17495480239189254581898527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11663653492792836387932351 17495480239189254581898527)
          ·
            refine ⟨26243220358783881872847791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17495480239189254581898527 26243220358783881872847791)
            ·
              refine ⟨39364830538175822809271687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26243220358783881872847791 39364830538175822809271687)
              ·
                refine ⟨59047245807263734213907531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39364830538175822809271687 59047245807263734213907531)
                ·
                  refine ⟨88570868710895601320861297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 59047245807263734213907531 88570868710895601320861297)
                  ·
                    refine ⟨66428151533171700990645973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 88570868710895601320861297 66428151533171700990645973)
                    ·
                      refine ⟨1556909801558711741968265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 66428151533171700990645973 1556909801558711741968265)
                      ·
                        rfl

theorem cell23_3032071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 1, 1, 2, 7].length) (baseStart_3032071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3032071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3032071 prefixEnd_3032071 := by exact prefixLift 3032071
  have htrace : WordTrace (prefixWord ++ tailWord_3032071) baseStart_3032071 baseEnd_3032071 := by
    simpa [prefixWord, tailWord_3032071, baseEnd_3032071] using wordTrace_append hprefix tailTrace_3032071
  have hstable : (prefixWord ++ tailWord_3032071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3032071).length < 2 ^ (prefixWord ++ tailWord_3032071).sum := by decide
  have hdescent : baseEnd_3032071 < baseStart_3032071 := by decide
  rcases family_descends (prefixWord ++ tailWord_3032071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3032078 : List Nat := [4, 1, 1, 2, 2, 2, 3, 1, 7]
def baseStart_3032078 : Nat := 118140960795 + 3032078 * 2 ^ 59
def prefixEnd_3032078 : Nat := 4983230072969 + 3 ^ 40 * 3032078 * 2
def baseEnd_3032078 : Nat := 172990377324810357175637

theorem tailTrace_3032078 : CollatzResearch.WordTrace tailWord_3032078 prefixEnd_3032078 172990377324810357175637 := by
  unfold tailWord_3032078
  simp only [CollatzResearch.WordTrace]
  refine ⟨13823621238663339817543111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 73725979939537812360229925 13823621238663339817543111)
  ·
    refine ⟨20735431857995009726314667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13823621238663339817543111 20735431857995009726314667)
    ·
      refine ⟨31103147786992514589472001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20735431857995009726314667 31103147786992514589472001)
      ·
        refine ⟨23327360840244385942104001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31103147786992514589472001 23327360840244385942104001)
        ·
          refine ⟨17495520630183289456578001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23327360840244385942104001 17495520630183289456578001)
          ·
            refine ⟨13121640472637467092433501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17495520630183289456578001 13121640472637467092433501)
            ·
              refine ⟨4920615177239050159662563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13121640472637467092433501 4920615177239050159662563)
              ·
                refine ⟨7380922765858575239493845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4920615177239050159662563 7380922765858575239493845)
                ·
                  refine ⟨172990377324810357175637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7380922765858575239493845 172990377324810357175637)
                  ·
                    rfl

theorem cell23_3032078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 3, 1, 7].length) (baseStart_3032078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3032078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3032078 prefixEnd_3032078 := by exact prefixLift 3032078
  have htrace : WordTrace (prefixWord ++ tailWord_3032078) baseStart_3032078 baseEnd_3032078 := by
    simpa [prefixWord, tailWord_3032078, baseEnd_3032078] using wordTrace_append hprefix tailTrace_3032078
  have hstable : (prefixWord ++ tailWord_3032078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3032078).length < 2 ^ (prefixWord ++ tailWord_3032078).sum := by decide
  have hdescent : baseEnd_3032078 < baseStart_3032078 := by decide
  rcases family_descends (prefixWord ++ tailWord_3032078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3032101 : List Nat := [1, 3, 1, 2, 2, 2, 1, 2, 1, 1, 7]
def baseStart_3032101 : Nat := 118140960795 + 3032101 * 2 ^ 59
def prefixEnd_3032101 : Nat := 4983230072969 + 3 ^ 40 * 3032101 * 2
def baseEnd_3032101 : Nat := 1556925205978346624593127

theorem tailTrace_3032101 : CollatzResearch.WordTrace tailWord_3032101 prefixEnd_3032101 1556925205978346624593127 := by
  unfold tailWord_3032101
  simp only [CollatzResearch.WordTrace]
  refine ⟨110589808788223393468432157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73726539192148928978954771 110589808788223393468432157)
  ·
    refine ⟨41471178295583772550662059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 110589808788223393468432157 41471178295583772550662059)
    ·
      refine ⟨62206767443375658825993089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41471178295583772550662059 62206767443375658825993089)
      ·
        refine ⟨46655075582531744119494817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62206767443375658825993089 46655075582531744119494817)
        ·
          refine ⟨34991306686898808089621113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46655075582531744119494817 34991306686898808089621113)
          ·
            refine ⟨26243480015174106067215835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34991306686898808089621113 26243480015174106067215835)
            ·
              refine ⟨39365220022761159100823753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26243480015174106067215835 39365220022761159100823753)
              ·
                refine ⟨29523915017070869325617815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39365220022761159100823753 29523915017070869325617815)
                ·
                  refine ⟨44285872525606303988426723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29523915017070869325617815 44285872525606303988426723)
                  ·
                    refine ⟨66428808788409455982640085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 44285872525606303988426723 66428808788409455982640085)
                    ·
                      refine ⟨1556925205978346624593127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 66428808788409455982640085 1556925205978346624593127)
                      ·
                        rfl

theorem cell23_3032101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 2, 1, 1, 7].length) (baseStart_3032101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3032101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3032101 prefixEnd_3032101 := by exact prefixLift 3032101
  have htrace : WordTrace (prefixWord ++ tailWord_3032101) baseStart_3032101 baseEnd_3032101 := by
    simpa [prefixWord, tailWord_3032101, baseEnd_3032101] using wordTrace_append hprefix tailTrace_3032101
  have hstable : (prefixWord ++ tailWord_3032101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3032101).length < 2 ^ (prefixWord ++ tailWord_3032101).sum := by decide
  have hdescent : baseEnd_3032101 < baseStart_3032101 := by decide
  rcases family_descends (prefixWord ++ tailWord_3032101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3032108 : List Nat := [2, 2, 1, 1, 1, 2, 6, 1, 2, 5]
def baseStart_3032108 : Nat := 118140960795 + 3032108 * 2 ^ 59
def prefixEnd_3032108 : Nat := 4983230072969 + 3 ^ 40 * 3032108 * 2
def baseEnd_3032108 : Nat := 518976266780976032401865

theorem tailTrace_3032108 : CollatzResearch.WordTrace tailWord_3032108 prefixEnd_3032108 518976266780976032401865 := by
  unfold tailWord_3032108
  simp only [CollatzResearch.WordTrace]
  refine ⟨55295032049599016831968489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73726709399465355775957985 55295032049599016831968489)
  ·
    refine ⟨41471274037199262623976367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55295032049599016831968489 41471274037199262623976367)
    ·
      refine ⟨62206911055798893935964551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41471274037199262623976367 62206911055798893935964551)
      ·
        refine ⟨93310366583698340903946827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62206911055798893935964551 93310366583698340903946827)
        ·
          refine ⟨139965549875547511355920241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93310366583698340903946827 139965549875547511355920241)
          ·
            refine ⟨104974162406660633516940181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 139965549875547511355920241 104974162406660633516940181)
            ·
              refine ⟨4920663862812217196106571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 104974162406660633516940181 4920663862812217196106571)
              ·
                refine ⟨7380995794218325794159857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4920663862812217196106571 7380995794218325794159857)
                ·
                  refine ⟨5535746845663744345619893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7380995794218325794159857 5535746845663744345619893)
                  ·
                    refine ⟨518976266780976032401865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5535746845663744345619893 518976266780976032401865)
                    ·
                      rfl

theorem cell23_3032108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 5].length) (baseStart_3032108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3032108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3032108 prefixEnd_3032108 := by exact prefixLift 3032108
  have htrace : WordTrace (prefixWord ++ tailWord_3032108) baseStart_3032108 baseEnd_3032108 := by
    simpa [prefixWord, tailWord_3032108, baseEnd_3032108] using wordTrace_append hprefix tailTrace_3032108
  have hstable : (prefixWord ++ tailWord_3032108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3032108).length < 2 ^ (prefixWord ++ tailWord_3032108).sum := by decide
  have hdescent : baseEnd_3032108 < baseStart_3032108 := by decide
  rcases family_descends (prefixWord ++ tailWord_3032108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3032111 : List Nat := [1, 1, 2, 1, 2, 1, 1, 2, 5, 3, 4]
def baseStart_3032111 : Nat := 118140960795 + 3032111 * 2 ^ 59
def prefixEnd_3032111 : Nat := 4983230072969 + 3 ^ 40 * 3032111 * 2
def baseEnd_3032111 : Nat := 1556930340784891585468081

theorem tailTrace_3032111 : CollatzResearch.WordTrace tailWord_3032111 prefixEnd_3032111 1556930340784891585468081 := by
  unfold tailWord_3032111
  simp only [CollatzResearch.WordTrace]
  refine ⟨110590173518187165176296187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73726782345458110117530791 110590173518187165176296187)
  ·
    refine ⟨165885260277280747764444281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110590173518187165176296187 165885260277280747764444281)
    ·
      refine ⟨124413945207960560823333211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 165885260277280747764444281 124413945207960560823333211)
      ·
        refine ⟨186620917811940841234999817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124413945207960560823333211 186620917811940841234999817)
        ·
          refine ⟨139965688358955630926249863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 186620917811940841234999817 139965688358955630926249863)
          ·
            refine ⟨209948532538433446389374795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 139965688358955630926249863 209948532538433446389374795)
            ·
              refine ⟨314922798807650169584062193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 209948532538433446389374795 314922798807650169584062193)
              ·
                refine ⟨236192099105737627188046645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 314922798807650169584062193 236192099105737627188046645)
                ·
                  refine ⟨22143009291162902548879373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 236192099105737627188046645 22143009291162902548879373)
                  ·
                    refine ⟨8303628484186088455829765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22143009291162902548879373 8303628484186088455829765)
                    ·
                      refine ⟨1556930340784891585468081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8303628484186088455829765 1556930340784891585468081)
                      ·
                        rfl

theorem cell23_3032111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 2, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 2, 5, 3, 4].length) (baseStart_3032111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3032111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3032111 prefixEnd_3032111 := by exact prefixLift 3032111
  have htrace : WordTrace (prefixWord ++ tailWord_3032111) baseStart_3032111 baseEnd_3032111 := by
    simpa [prefixWord, tailWord_3032111, baseEnd_3032111] using wordTrace_append hprefix tailTrace_3032111
  have hstable : (prefixWord ++ tailWord_3032111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3032111).length < 2 ^ (prefixWord ++ tailWord_3032111).sum := by decide
  have hdescent : baseEnd_3032111 < baseStart_3032111 := by decide
  rcases family_descends (prefixWord ++ tailWord_3032111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3032128 : List Nat := [2, 1, 1, 2, 2, 3, 1, 4, 2, 1, 4]
def baseStart_3032128 : Nat := 118140960795 + 3032128 * 2 ^ 59
def prefixEnd_3032128 : Nat := 4983230072969 + 3 ^ 40 * 3032128 * 2
def baseEnd_3032128 : Nat := 1556939069956018018955503

theorem tailTrace_3032128 : CollatzResearch.WordTrace tailWord_3032128 prefixEnd_3032128 1556939069956018018955503 := by
  unfold tailWord_3032128
  simp only [CollatzResearch.WordTrace]
  refine ⟨55295396779562788539832519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73727195706083718053110025 55295396779562788539832519)
  ·
    refine ⟨82943095169344182809748779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55295396779562788539832519 82943095169344182809748779)
    ·
      refine ⟨124414642754016274214623169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82943095169344182809748779 124414642754016274214623169)
      ·
        refine ⟨93310982065512205660967377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 124414642754016274214623169 93310982065512205660967377)
        ·
          refine ⟨69983236549134154245725533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93310982065512205660967377 69983236549134154245725533)
          ·
            refine ⟨26243713705925307842147075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 69983236549134154245725533 26243713705925307842147075)
            ·
              refine ⟨39365570558887961763220613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26243713705925307842147075 39365570558887961763220613)
              ·
                refine ⟨7381044479791492830603865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39365570558887961763220613 7381044479791492830603865)
                ·
                  refine ⟨5535783359843619622952899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7381044479791492830603865 5535783359843619622952899)
                  ·
                    refine ⟨8303675039765429434429349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5535783359843619622952899 8303675039765429434429349)
                    ·
                      refine ⟨1556939069956018018955503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8303675039765429434429349 1556939069956018018955503)
                      ·
                        rfl

theorem cell23_3032128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 4, 2, 1, 4].length) (baseStart_3032128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3032128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3032128 prefixEnd_3032128 := by exact prefixLift 3032128
  have htrace : WordTrace (prefixWord ++ tailWord_3032128) baseStart_3032128 baseEnd_3032128 := by
    simpa [prefixWord, tailWord_3032128, baseEnd_3032128] using wordTrace_append hprefix tailTrace_3032128
  have hstable : (prefixWord ++ tailWord_3032128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3032128).length < 2 ^ (prefixWord ++ tailWord_3032128).sum := by decide
  have hdescent : baseEnd_3032128 < baseStart_3032128 := by decide
  rcases family_descends (prefixWord ++ tailWord_3032128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3032129 : List Nat := [1, 2, 5, 1, 3, 2, 2, 2, 5]
def baseStart_3032129 : Nat := 118140960795 + 3032129 * 2 ^ 59
def prefixEnd_3032129 : Nat := 4983230072969 + 3 ^ 40 * 3032129 * 2
def baseEnd_3032129 : Nat := 172993287048519168338111

theorem tailTrace_3032129 : CollatzResearch.WordTrace tailWord_3032129 prefixEnd_3032129 172993287048519168338111 := by
  unfold tailWord_3032129
  simp only [CollatzResearch.WordTrace]
  refine ⟨110590830032121954250451441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73727220021414636166967627 110590830032121954250451441)
  ·
    refine ⟨82943122524091465687838581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110590830032121954250451441 82943122524091465687838581)
    ·
      refine ⟨7775917736633574908234867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 82943122524091465687838581 7775917736633574908234867)
      ·
        refine ⟨11663876604950362362352301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7775917736633574908234867 11663876604950362362352301)
        ·
          refine ⟨4373953726856385885882113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11663876604950362362352301 4373953726856385885882113)
          ·
            refine ⟨3280465295142289414411585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4373953726856385885882113 3280465295142289414411585)
            ·
              refine ⟨2460348971356717060808689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3280465295142289414411585 2460348971356717060808689)
              ·
                refine ⟨1845261728517537795606517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2460348971356717060808689 1845261728517537795606517)
                ·
                  refine ⟨172993287048519168338111, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1845261728517537795606517 172993287048519168338111)
                  ·
                    rfl

theorem cell23_3032129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 2, 2, 2, 5].length) (baseStart_3032129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3032129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3032129 prefixEnd_3032129 := by exact prefixLift 3032129
  have htrace : WordTrace (prefixWord ++ tailWord_3032129) baseStart_3032129 baseEnd_3032129 := by
    simpa [prefixWord, tailWord_3032129, baseEnd_3032129] using wordTrace_append hprefix tailTrace_3032129
  have hstable : (prefixWord ++ tailWord_3032129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3032129).length < 2 ^ (prefixWord ++ tailWord_3032129).sum := by decide
  have hdescent : baseEnd_3032129 < baseStart_3032129 := by decide
  rcases family_descends (prefixWord ++ tailWord_3032129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3032131 : List Nat := [1, 1, 1, 3, 1, 2, 3, 1, 2, 3, 5]
def baseStart_3032131 : Nat := 118140960795 + 3032131 * 2 ^ 59
def prefixEnd_3032131 : Nat := 4983230072969 + 3 ^ 40 * 3032131 * 2
def baseEnd_3032131 : Nat := 1556940610397981507217989

theorem tailTrace_3032131 : CollatzResearch.WordTrace tailWord_3032131 prefixEnd_3032131 1556940610397981507217989 := by
  unfold tailWord_3032131
  simp only [CollatzResearch.WordTrace]
  refine ⟨110590902978114708592024247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73727268652076472394682831 110590902978114708592024247)
  ·
    refine ⟨165886354467172062888036371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110590902978114708592024247 165886354467172062888036371)
    ·
      refine ⟨248829531700758094332054557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165886354467172062888036371 248829531700758094332054557)
      ·
        refine ⟨93311074387784285374520459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 248829531700758094332054557 93311074387784285374520459)
        ·
          refine ⟨139966611581676428061780689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93311074387784285374520459 139966611581676428061780689)
          ·
            refine ⟨104974958686257321046335517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 139966611581676428061780689 104974958686257321046335517)
            ·
              refine ⟨39365609507346495392375819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 104974958686257321046335517 39365609507346495392375819)
              ·
                refine ⟨59048414261019743088563729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39365609507346495392375819 59048414261019743088563729)
                ·
                  refine ⟨44286310695764807316422797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 59048414261019743088563729 44286310695764807316422797)
                  ·
                    refine ⟨16607366510911802743658549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 44286310695764807316422797 16607366510911802743658549)
                    ·
                      refine ⟨1556940610397981507217989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16607366510911802743658549 1556940610397981507217989)
                      ·
                        rfl

theorem cell23_3032131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 1, 2, 3, 5].length) (baseStart_3032131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3032131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3032131 prefixEnd_3032131 := by exact prefixLift 3032131
  have htrace : WordTrace (prefixWord ++ tailWord_3032131) baseStart_3032131 baseEnd_3032131 := by
    simpa [prefixWord, tailWord_3032131, baseEnd_3032131] using wordTrace_append hprefix tailTrace_3032131
  have hstable : (prefixWord ++ tailWord_3032131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3032131).length < 2 ^ (prefixWord ++ tailWord_3032131).sum := by decide
  have hdescent : baseEnd_3032131 < baseStart_3032131 := by decide
  rcases family_descends (prefixWord ++ tailWord_3032131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3032151 : List Nat := [1, 1, 3, 2, 2, 1, 1, 2, 10]
def baseStart_3032151 : Nat := 118140960795 + 3032151 * 2 ^ 59
def prefixEnd_3032151 : Nat := 4983230072969 + 3 ^ 40 * 3032151 * 2
def baseEnd_3032151 : Nat := 172994542223452380996433

theorem tailTrace_3032151 : CollatzResearch.WordTrace tailWord_3032151 prefixEnd_3032151 172994542223452380996433 := by
  unfold tailWord_3032151
  simp only [CollatzResearch.WordTrace]
  refine ⟨110591632438042252007752307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73727754958694834671834871 110591632438042252007752307)
  ·
    refine ⟨165887448657063378011628461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110591632438042252007752307 165887448657063378011628461)
    ·
      refine ⟨62207793246398766754360673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 165887448657063378011628461 62207793246398766754360673)
      ·
        refine ⟨46655844934799075065770505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62207793246398766754360673 46655844934799075065770505)
        ·
          refine ⟨34991883701099306299327879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46655844934799075065770505 34991883701099306299327879)
          ·
            refine ⟨52487825551648959448991819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34991883701099306299327879 52487825551648959448991819)
            ·
              refine ⟨78731738327473439173487729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52487825551648959448991819 78731738327473439173487729)
              ·
                refine ⟨59048803745605079380115797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 78731738327473439173487729 59048803745605079380115797)
                ·
                  refine ⟨172994542223452380996433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 59048803745605079380115797 172994542223452380996433)
                  ·
                    rfl

theorem cell23_3032151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 2, 10].length) (baseStart_3032151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3032151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3032151 prefixEnd_3032151 := by exact prefixLift 3032151
  have htrace : WordTrace (prefixWord ++ tailWord_3032151) baseStart_3032151 baseEnd_3032151 := by
    simpa [prefixWord, tailWord_3032151, baseEnd_3032151] using wordTrace_append hprefix tailTrace_3032151
  have hstable : (prefixWord ++ tailWord_3032151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3032151).length < 2 ^ (prefixWord ++ tailWord_3032151).sum := by decide
  have hdescent : baseEnd_3032151 < baseStart_3032151 := by decide
  rcases family_descends (prefixWord ++ tailWord_3032151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3032162 : List Nat := [3, 3, 2, 2, 1, 1, 3, 1, 2, 1, 4]
def baseStart_3032162 : Nat := 118140960795 + 3032162 * 2 ^ 59
def prefixEnd_3032162 : Nat := 4983230072969 + 3 ^ 40 * 3032162 * 2
def baseEnd_3032162 : Nat := 1556956528298270885930347

theorem tailTrace_3032162 : CollatzResearch.WordTrace tailWord_3032162 prefixEnd_3032162 1556956528298270885930347 := by
  unfold tailWord_3032162
  simp only [CollatzResearch.WordTrace]
  refine ⟨27648008410250600221600685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73728022427334933924268493 27648008410250600221600685)
  ·
    refine ⟨10368003153843975083100257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27648008410250600221600685 10368003153843975083100257)
    ·
      refine ⟨7776002365382981312325193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10368003153843975083100257 7776002365382981312325193)
      ·
        refine ⟨5832001774037235984243895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7776002365382981312325193 5832001774037235984243895)
        ·
          refine ⟨8748002661055853976365843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5832001774037235984243895 8748002661055853976365843)
          ·
            refine ⟨13122003991583780964548765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8748002661055853976365843 13122003991583780964548765)
            ·
              refine ⟨4920751496843917861705787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13122003991583780964548765 4920751496843917861705787)
              ·
                refine ⟨7381127245265876792558681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4920751496843917861705787 7381127245265876792558681)
                ·
                  refine ⟨5535845433949407594419011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7381127245265876792558681 5535845433949407594419011)
                  ·
                    refine ⟨8303768150924111391628517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5535845433949407594419011 8303768150924111391628517)
                    ·
                      refine ⟨1556956528298270885930347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8303768150924111391628517 1556956528298270885930347)
                      ·
                        rfl

theorem cell23_3032162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 3, 1, 2, 1, 4].length) (baseStart_3032162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3032162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3032162 prefixEnd_3032162 := by exact prefixLift 3032162
  have htrace : WordTrace (prefixWord ++ tailWord_3032162) baseStart_3032162 baseEnd_3032162 := by
    simpa [prefixWord, tailWord_3032162, baseEnd_3032162] using wordTrace_append hprefix tailTrace_3032162
  have hstable : (prefixWord ++ tailWord_3032162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3032162).length < 2 ^ (prefixWord ++ tailWord_3032162).sum := by decide
  have hdescent : baseEnd_3032162 < baseStart_3032162 := by decide
  rcases family_descends (prefixWord ++ tailWord_3032162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3032171 : List Nat := [1, 1, 1, 1, 2, 2, 1, 1, 5, 2, 6]
def baseStart_3032171 : Nat := 118140960795 + 3032171 * 2 ^ 59
def prefixEnd_3032171 : Nat := 4983230072969 + 3 ^ 40 * 3032171 * 2
def baseEnd_3032171 : Nat := 1556961149624161350717805

theorem tailTrace_3032171 : CollatzResearch.WordTrace tailWord_3032171 prefixEnd_3032171 1556961149624161350717805 := by
  unfold tailWord_3032171
  simp only [CollatzResearch.WordTrace]
  refine ⟨110592361897969795423480367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73728241265313196948986911 110592361897969795423480367)
  ·
    refine ⟨165888542846954693135220551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110592361897969795423480367 165888542846954693135220551)
    ·
      refine ⟨248832814270432039702830827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165888542846954693135220551 248832814270432039702830827)
      ·
        refine ⟨373249221405648059554246241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 248832814270432039702830827 373249221405648059554246241)
        ·
          refine ⟨279936916054236044665684681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 373249221405648059554246241 279936916054236044665684681)
          ·
            refine ⟨209952687040677033499263511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 279936916054236044665684681 209952687040677033499263511)
            ·
              refine ⟨314929030561015550248895267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 209952687040677033499263511 314929030561015550248895267)
              ·
                refine ⟨472393545841523325373342901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 314929030561015550248895267 472393545841523325373342901)
                ·
                  refine ⟨44286894922642811753750897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 472393545841523325373342901 44286894922642811753750897)
                  ·
                    refine ⟨33215171191982108815313173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 44286894922642811753750897 33215171191982108815313173)
                    ·
                      refine ⟨1556961149624161350717805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 33215171191982108815313173 1556961149624161350717805)
                      ·
                        rfl

theorem cell23_3032171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 1, 5, 2, 6].length) (baseStart_3032171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3032171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3032171 prefixEnd_3032171 := by exact prefixLift 3032171
  have htrace : WordTrace (prefixWord ++ tailWord_3032171) baseStart_3032171 baseEnd_3032171 := by
    simpa [prefixWord, tailWord_3032171, baseEnd_3032171] using wordTrace_append hprefix tailTrace_3032171
  have hstable : (prefixWord ++ tailWord_3032171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3032171).length < 2 ^ (prefixWord ++ tailWord_3032171).sum := by decide
  have hdescent : baseEnd_3032171 < baseStart_3032171 := by decide
  rcases family_descends (prefixWord ++ tailWord_3032171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3032172 : List Nat := [2, 2, 1, 1, 3, 2, 4, 3, 1, 4]
def baseStart_3032172 : Nat := 118140960795 + 3032172 * 2 ^ 59
def prefixEnd_3032172 : Nat := 4983230072969 + 3 ^ 40 * 3032172 * 2
def baseEnd_3032172 : Nat := 518987221034938615601767

theorem tailTrace_3032172 : CollatzResearch.WordTrace tailWord_3032172 prefixEnd_3032172 518987221034938615601767 := by
  unfold tailWord_3032172
  simp only [CollatzResearch.WordTrace]
  refine ⟨55296199185483086297133385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73728265580644115062844513 55296199185483086297133385)
  ·
    refine ⟨41472149389112314722850039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55296199185483086297133385 41472149389112314722850039)
    ·
      refine ⟨62208224083668472084275059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41472149389112314722850039 62208224083668472084275059)
      ·
        refine ⟨93312336125502708126412589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62208224083668472084275059 93312336125502708126412589)
        ·
          refine ⟨34992126047063515547404721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 93312336125502708126412589 34992126047063515547404721)
          ·
            refine ⟨26244094535297636660553541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34992126047063515547404721 26244094535297636660553541)
            ·
              refine ⟨4920767725368306873853789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26244094535297636660553541 4920767725368306873853789)
              ·
                refine ⟨1845287897013115077695171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4920767725368306873853789 1845287897013115077695171)
                ·
                  refine ⟨2767931845519672616542757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1845287897013115077695171 2767931845519672616542757)
                  ·
                    refine ⟨518987221034938615601767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2767931845519672616542757 518987221034938615601767)
                    ·
                      rfl

theorem cell23_3032172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 4, 3, 1, 4].length) (baseStart_3032172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3032172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3032172 prefixEnd_3032172 := by exact prefixLift 3032172
  have htrace : WordTrace (prefixWord ++ tailWord_3032172) baseStart_3032172 baseEnd_3032172 := by
    simpa [prefixWord, tailWord_3032172, baseEnd_3032172] using wordTrace_append hprefix tailTrace_3032172
  have hstable : (prefixWord ++ tailWord_3032172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3032172).length < 2 ^ (prefixWord ++ tailWord_3032172).sum := by decide
  have hdescent : baseEnd_3032172 < baseStart_3032172 := by decide
  rcases family_descends (prefixWord ++ tailWord_3032172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3032215 : List Nat := [1, 1, 3, 3, 3, 1, 1, 4, 1, 5]
def baseStart_3032215 : Nat := 118140960795 + 3032215 * 2 ^ 59
def prefixEnd_3032215 : Nat := 4983230072969 + 3 ^ 40 * 3032215 * 2
def baseEnd_3032215 : Nat := 518994580924319726189201

theorem tailTrace_3032215 : CollatzResearch.WordTrace tailWord_3032215 prefixEnd_3032215 518994580924319726189201 := by
  unfold tailWord_3032215
  simp only [CollatzResearch.WordTrace]
  refine ⟨110593966709810390938082099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73729311139873593958721399 110593966709810390938082099)
  ·
    refine ⟨165890950064715586407123149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110593966709810390938082099 165890950064715586407123149)
    ·
      refine ⟨62209106274268344902671181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 165890950064715586407123149 62209106274268344902671181)
      ·
        refine ⟨23328414852850629338501693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62209106274268344902671181 23328414852850629338501693)
        ·
          refine ⟨8748155569818986001938135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23328414852850629338501693 8748155569818986001938135)
          ·
            refine ⟨13122233354728479002907203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8748155569818986001938135 13122233354728479002907203)
            ·
              refine ⟨19683350032092718504360805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13122233354728479002907203 19683350032092718504360805)
              ·
                refine ⟨3690628131017384719567651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19683350032092718504360805 3690628131017384719567651)
                ·
                  refine ⟨5535942196526077079351477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3690628131017384719567651 5535942196526077079351477)
                  ·
                    refine ⟨518994580924319726189201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5535942196526077079351477 518994580924319726189201)
                    ·
                      rfl

theorem cell23_3032215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 1, 4, 1, 5].length) (baseStart_3032215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3032215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3032215 prefixEnd_3032215 := by exact prefixLift 3032215
  have htrace : WordTrace (prefixWord ++ tailWord_3032215) baseStart_3032215 baseEnd_3032215 := by
    simpa [prefixWord, tailWord_3032215, baseEnd_3032215] using wordTrace_append hprefix tailTrace_3032215
  have hstable : (prefixWord ++ tailWord_3032215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3032215).length < 2 ^ (prefixWord ++ tailWord_3032215).sum := by decide
  have hdescent : baseEnd_3032215 < baseStart_3032215 := by decide
  rcases family_descends (prefixWord ++ tailWord_3032215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3032229 : List Nat := [1, 3, 1, 2, 1, 4, 3, 3, 1, 1, 3]
def baseStart_3032229 : Nat := 118140960795 + 3032229 * 2 ^ 59
def prefixEnd_3032229 : Nat := 4983230072969 + 3 ^ 40 * 3032229 * 2
def baseEnd_3032229 : Nat := 1556990931502122123792539

theorem tailTrace_3032229 : CollatzResearch.WordTrace tailWord_3032229 prefixEnd_3032229 1556990931502122123792539 := by
  unfold tailWord_3032229
  simp only [CollatzResearch.WordTrace]
  refine ⟨110594477331759671329091741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73729651554506447552727827 110594477331759671329091741)
  ·
    refine ⟨41472928999409876748409403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 110594477331759671329091741 41472928999409876748409403)
    ·
      refine ⟨62209393499114815122614105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41472928999409876748409403 62209393499114815122614105)
      ·
        refine ⟨46657045124336111341960579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62209393499114815122614105 46657045124336111341960579)
        ·
          refine ⟨69985567686504167012940869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46657045124336111341960579 69985567686504167012940869)
          ·
            refine ⟨13122293941219531314926413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 69985567686504167012940869 13122293941219531314926413)
            ·
              refine ⟨4920860227957324243097405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13122293941219531314926413 4920860227957324243097405)
              ·
                refine ⟨1845322585483996591161527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4920860227957324243097405 1845322585483996591161527)
                ·
                  refine ⟨2767983878225994886742291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1845322585483996591161527 2767983878225994886742291)
                  ·
                    refine ⟨4151975817338992330113437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2767983878225994886742291 4151975817338992330113437)
                    ·
                      refine ⟨1556990931502122123792539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4151975817338992330113437 1556990931502122123792539)
                      ·
                        rfl

theorem cell23_3032229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 3, 3, 1, 1, 3].length) (baseStart_3032229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3032229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3032229 prefixEnd_3032229 := by exact prefixLift 3032229
  have htrace : WordTrace (prefixWord ++ tailWord_3032229) baseStart_3032229 baseEnd_3032229 := by
    simpa [prefixWord, tailWord_3032229, baseEnd_3032229] using wordTrace_append hprefix tailTrace_3032229
  have hstable : (prefixWord ++ tailWord_3032229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3032229).length < 2 ^ (prefixWord ++ tailWord_3032229).sum := by decide
  have hdescent : baseEnd_3032229 < baseStart_3032229 := by decide
  rcases family_descends (prefixWord ++ tailWord_3032229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3032248 : List Nat := [2, 1, 2, 1, 2, 1, 2, 1, 5, 2, 4]
def baseStart_3032248 : Nat := 118140960795 + 3032248 * 2 ^ 59
def prefixEnd_3032248 : Nat := 4983230072969 + 3 ^ 40 * 3032248 * 2
def baseEnd_3032248 : Nat := 1557000687634557549454951

theorem tailTrace_3032248 : CollatzResearch.WordTrace tailWord_3032248 prefixEnd_3032248 1557000687634557549454951 := by
  unfold tailWord_3032248
  simp only [CollatzResearch.WordTrace]
  refine ⟨55297585159345418787016699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73730113545793891716022265 55297585159345418787016699)
  ·
    refine ⟨82946377739018128180525049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55297585159345418787016699 82946377739018128180525049)
    ·
      refine ⟨62209783304263596135393787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82946377739018128180525049 62209783304263596135393787)
      ·
        refine ⟨93314674956395394203090681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62209783304263596135393787 93314674956395394203090681)
        ·
          refine ⟨69986006217296545652318011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93314674956395394203090681 69986006217296545652318011)
          ·
            refine ⟨104979009325944818478477017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69986006217296545652318011 104979009325944818478477017)
            ·
              refine ⟨78734256994458613858857763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 104979009325944818478477017 78734256994458613858857763)
              ·
                refine ⟨118101385491687920788286645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 78734256994458613858857763 118101385491687920788286645)
                ·
                  refine ⟨11072004889845742573901873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 118101385491687920788286645 11072004889845742573901873)
                  ·
                    refine ⟨8304003667384306930426405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11072004889845742573901873 8304003667384306930426405)
                    ·
                      refine ⟨1557000687634557549454951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8304003667384306930426405 1557000687634557549454951)
                      ·
                        rfl

theorem cell23_3032248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 1, 5, 2, 4].length) (baseStart_3032248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3032248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3032248 prefixEnd_3032248 := by exact prefixLift 3032248
  have htrace : WordTrace (prefixWord ++ tailWord_3032248) baseStart_3032248 baseEnd_3032248 := by
    simpa [prefixWord, tailWord_3032248, baseEnd_3032248] using wordTrace_append hprefix tailTrace_3032248
  have hstable : (prefixWord ++ tailWord_3032248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3032248).length < 2 ^ (prefixWord ++ tailWord_3032248).sum := by decide
  have hdescent : baseEnd_3032248 < baseStart_3032248 := by decide
  rcases family_descends (prefixWord ++ tailWord_3032248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3032289 : List Nat := [1, 2, 3, 1, 3, 3, 3, 1, 1, 2, 3]
def baseStart_3032289 : Nat := 118140960795 + 3032289 * 2 ^ 59
def prefixEnd_3032289 : Nat := 4983230072969 + 3 ^ 40 * 3032289 * 2
def baseEnd_3032289 : Nat := 1557021740341391889042263

theorem tailTrace_3032289 : CollatzResearch.WordTrace tailWord_3032289 prefixEnd_3032289 1557021740341391889042263 := by
  unfold tailWord_3032289
  simp only [CollatzResearch.WordTrace]
  refine ⟨110596665711542301576275921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73731110474361534384183947 110596665711542301576275921)
  ·
    refine ⟨82947499283656726182206941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110596665711542301576275921 82947499283656726182206941)
    ·
      refine ⟨31105312231371272318327603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82947499283656726182206941 31105312231371272318327603)
      ·
        refine ⟨46657968347056908477491405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31105312231371272318327603 46657968347056908477491405)
        ·
          refine ⟨17496738130146340679059277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46657968347056908477491405 17496738130146340679059277)
          ·
            refine ⟨6561276798804877754647229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17496738130146340679059277 6561276798804877754647229)
            ·
              refine ⟨2460478799551829157992711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6561276798804877754647229 2460478799551829157992711)
              ·
                refine ⟨3690718199327743736989067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2460478799551829157992711 3690718199327743736989067)
                ·
                  refine ⟨5536077298991615605483601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3690718199327743736989067 5536077298991615605483601)
                  ·
                    refine ⟨4152057974243711704112701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5536077298991615605483601 4152057974243711704112701)
                    ·
                      refine ⟨1557021740341391889042263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4152057974243711704112701 1557021740341391889042263)
                      ·
                        rfl

theorem cell23_3032289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 3, 1, 1, 2, 3].length) (baseStart_3032289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3032289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3032289 prefixEnd_3032289 := by exact prefixLift 3032289
  have htrace : WordTrace (prefixWord ++ tailWord_3032289) baseStart_3032289 baseEnd_3032289 := by
    simpa [prefixWord, tailWord_3032289, baseEnd_3032289] using wordTrace_append hprefix tailTrace_3032289
  have hstable : (prefixWord ++ tailWord_3032289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3032289).length < 2 ^ (prefixWord ++ tailWord_3032289).sum := by decide
  have hdescent : baseEnd_3032289 < baseStart_3032289 := by decide
  rcases family_descends (prefixWord ++ tailWord_3032289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3032302 : List Nat := [4, 1, 2, 1, 1, 1, 2, 3, 4, 1, 3]
def baseStart_3032302 : Nat := 118140960795 + 3032302 * 2 ^ 59
def prefixEnd_3032302 : Nat := 4983230072969 + 3 ^ 40 * 3032302 * 2
def baseEnd_3032302 : Nat := 1557028415589900338179703

theorem tailTrace_3032302 : CollatzResearch.WordTrace tailWord_3032302 prefixEnd_3032302 1557028415589900338179703 := by
  unfold tailWord_3032302
  simp only [CollatzResearch.WordTrace]
  refine ⟨13824642482561900599562395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 73731426573663469864332773 13824642482561900599562395)
  ·
    refine ⟨20736963723842850899343593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13824642482561900599562395 20736963723842850899343593)
    ·
      refine ⟨15552722792882138174507695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20736963723842850899343593 15552722792882138174507695)
      ·
        refine ⟨23329084189323207261761543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15552722792882138174507695 23329084189323207261761543)
        ·
          refine ⟨34993626283984810892642315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23329084189323207261761543 34993626283984810892642315)
          ·
            refine ⟨52490439425977216338963473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34993626283984810892642315 52490439425977216338963473)
            ·
              refine ⟨39367829569482912254222605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52490439425977216338963473 39367829569482912254222605)
              ·
                refine ⟨14762936088556092095333477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39367829569482912254222605 14762936088556092095333477)
                ·
                  refine ⟨2768050516604267267875027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14762936088556092095333477 2768050516604267267875027)
                  ·
                    refine ⟨4152075774906400901812541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2768050516604267267875027 4152075774906400901812541)
                    ·
                      refine ⟨1557028415589900338179703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4152075774906400901812541 1557028415589900338179703)
                      ·
                        rfl

theorem cell23_3032302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 3, 4, 1, 3].length) (baseStart_3032302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3032302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3032302 prefixEnd_3032302 := by exact prefixLift 3032302
  have htrace : WordTrace (prefixWord ++ tailWord_3032302) baseStart_3032302 baseEnd_3032302 := by
    simpa [prefixWord, tailWord_3032302, baseEnd_3032302] using wordTrace_append hprefix tailTrace_3032302
  have hstable : (prefixWord ++ tailWord_3032302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3032302).length < 2 ^ (prefixWord ++ tailWord_3032302).sum := by decide
  have hdescent : baseEnd_3032302 < baseStart_3032302 := by decide
  rcases family_descends (prefixWord ++ tailWord_3032302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3032346 : List Nat := [3, 1, 1, 3, 3, 1, 4, 1, 1, 3, 2]
def baseStart_3032346 : Nat := 118140960795 + 3032346 * 2 ^ 59
def prefixEnd_3032346 : Nat := 4983230072969 + 3 ^ 40 * 3032346 * 2
def baseEnd_3032346 : Nat := 1557051008738698166029501

theorem tailTrace_3032346 : CollatzResearch.WordTrace tailWord_3032346 prefixEnd_3032346 1557051008738698166029501 := by
  unfold tailWord_3032346
  simp only [CollatzResearch.WordTrace]
  refine ⟨27649686168083950077775223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73732496448223866874067261 27649686168083950077775223)
  ·
    refine ⟨41474529252125925116662835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27649686168083950077775223 41474529252125925116662835)
    ·
      refine ⟨62211793878188887674994253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41474529252125925116662835 62211793878188887674994253)
      ·
        refine ⟨23329422704320832878122845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62211793878188887674994253 23329422704320832878122845)
        ·
          refine ⟨8748533514120312329296067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23329422704320832878122845 8748533514120312329296067)
          ·
            refine ⟨13122800271180468493944101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8748533514120312329296067 13122800271180468493944101)
            ·
              refine ⟨2460525050846337842614519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13122800271180468493944101 2460525050846337842614519)
              ·
                refine ⟨3690787576269506763921779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2460525050846337842614519 3690787576269506763921779)
                ·
                  refine ⟨5536181364404260145882669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3690787576269506763921779 5536181364404260145882669)
                  ·
                    refine ⟨2076068011651597554706001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5536181364404260145882669 2076068011651597554706001)
                    ·
                      refine ⟨1557051008738698166029501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2076068011651597554706001 1557051008738698166029501)
                      ·
                        rfl

theorem cell23_3032346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 4, 1, 1, 3, 2].length) (baseStart_3032346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3032346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3032346 prefixEnd_3032346 := by exact prefixLift 3032346
  have htrace : WordTrace (prefixWord ++ tailWord_3032346) baseStart_3032346 baseEnd_3032346 := by
    simpa [prefixWord, tailWord_3032346, baseEnd_3032346] using wordTrace_append hprefix tailTrace_3032346
  have hstable : (prefixWord ++ tailWord_3032346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3032346).length < 2 ^ (prefixWord ++ tailWord_3032346).sum := by decide
  have hdescent : baseEnd_3032346 < baseStart_3032346 := by decide
  rcases family_descends (prefixWord ++ tailWord_3032346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3032355 : List Nat := [1, 1, 1, 4, 2, 3, 1, 2, 2, 2, 4]
def baseStart_3032355 : Nat := 118140960795 + 3032355 * 2 ^ 59
def prefixEnd_3032355 : Nat := 4983230072969 + 3 ^ 40 * 3032355 * 2
def baseEnd_3032355 : Nat := 1557055630064588630816959

theorem tailTrace_3032355 : CollatzResearch.WordTrace tailWord_3032355 prefixEnd_3032355 1557055630064588630816959 := by
  unfold tailWord_3032355
  simp only [CollatzResearch.WordTrace]
  refine ⟨110599072929303194848178519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73732715286202129898785679 110599072929303194848178519)
  ·
    refine ⟨165898609393954792272267779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110599072929303194848178519 165898609393954792272267779)
    ·
      refine ⟨248847914090932188408401669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165898609393954792272267779 248847914090932188408401669)
      ·
        refine ⟨46658983892049785326575313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 248847914090932188408401669 46658983892049785326575313)
        ·
          refine ⟨34994237919037338994931485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46658983892049785326575313 34994237919037338994931485)
          ·
            refine ⟨13122839219639002123099307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34994237919037338994931485 13122839219639002123099307)
            ·
              refine ⟨19684258829458503184648961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13122839219639002123099307 19684258829458503184648961)
              ·
                refine ⟨14763194122093877388486721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19684258829458503184648961 14763194122093877388486721)
                ·
                  refine ⟨11072395591570408041365041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14763194122093877388486721 11072395591570408041365041)
                  ·
                    refine ⟨8304296693677806031023781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11072395591570408041365041 8304296693677806031023781)
                    ·
                      refine ⟨1557055630064588630816959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8304296693677806031023781 1557055630064588630816959)
                      ·
                        rfl

theorem cell23_3032355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 1, 2, 2, 2, 4].length) (baseStart_3032355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3032355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3032355 prefixEnd_3032355 := by exact prefixLift 3032355
  have htrace : WordTrace (prefixWord ++ tailWord_3032355) baseStart_3032355 baseEnd_3032355 := by
    simpa [prefixWord, tailWord_3032355, baseEnd_3032355] using wordTrace_append hprefix tailTrace_3032355
  have hstable : (prefixWord ++ tailWord_3032355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3032355).length < 2 ^ (prefixWord ++ tailWord_3032355).sum := by decide
  have hdescent : baseEnd_3032355 < baseStart_3032355 := by decide
  rcases family_descends (prefixWord ++ tailWord_3032355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3032372 : List Nat := [2, 5, 1, 1, 1, 1, 1, 3, 2, 2, 4]
def baseStart_3032372 : Nat := 118140960795 + 3032372 * 2 ^ 59
def prefixEnd_3032372 : Nat := 4983230072969 + 3 ^ 40 * 3032372 * 2
def baseEnd_3032372 : Nat := 1557064359235715064304381

theorem tailTrace_3032372 : CollatzResearch.WordTrace tailWord_3032372 prefixEnd_3032372 1557064359235715064304381 := by
  unfold tailWord_3032372
  simp only [CollatzResearch.WordTrace]
  refine ⟨55299846485120803375773685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73733128646827737834364913 55299846485120803375773685)
  ·
    refine ⟨5184360607980075316478783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 55299846485120803375773685 5184360607980075316478783)
    ·
      refine ⟨7776540911970112974718175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5184360607980075316478783 7776540911970112974718175)
      ·
        refine ⟨11664811367955169462077263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7776540911970112974718175 11664811367955169462077263)
        ·
          refine ⟨17497217051932754193115895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11664811367955169462077263 17497217051932754193115895)
          ·
            refine ⟨26245825577899131289673843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17497217051932754193115895 26245825577899131289673843)
            ·
              refine ⟨39368738366848696934510765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26245825577899131289673843 39368738366848696934510765)
              ·
                refine ⟨14763276887568261350441537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39368738366848696934510765 14763276887568261350441537)
                ·
                  refine ⟨11072457665676196012831153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14763276887568261350441537 11072457665676196012831153)
                  ·
                    refine ⟨8304343249257147009623365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11072457665676196012831153 8304343249257147009623365)
                    ·
                      refine ⟨1557064359235715064304381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8304343249257147009623365 1557064359235715064304381)
                      ·
                        rfl

theorem cell23_3032372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 3, 2, 2, 4].length) (baseStart_3032372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3032372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3032372 prefixEnd_3032372 := by exact prefixLift 3032372
  have htrace : WordTrace (prefixWord ++ tailWord_3032372) baseStart_3032372 baseEnd_3032372 := by
    simpa [prefixWord, tailWord_3032372, baseEnd_3032372] using wordTrace_append hprefix tailTrace_3032372
  have hstable : (prefixWord ++ tailWord_3032372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3032372).length < 2 ^ (prefixWord ++ tailWord_3032372).sum := by decide
  have hdescent : baseEnd_3032372 < baseStart_3032372 := by decide
  rcases family_descends (prefixWord ++ tailWord_3032372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3032402 : List Nat := [3, 2, 2, 1, 1, 1, 1, 2, 1, 7, 2]
def baseStart_3032402 : Nat := 118140960795 + 3032402 * 2 ^ 59
def prefixEnd_3032402 : Nat := 4983230072969 + 3 ^ 40 * 3032402 * 2
def baseEnd_3032402 : Nat := 1557079763655349946929243

theorem tailTrace_3032402 : CollatzResearch.WordTrace tailWord_3032402 prefixEnd_3032402 1557079763655349946929243 := by
  unfold tailWord_3032402
  simp only [CollatzResearch.WordTrace]
  refine ⟨27650196790033230468784865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73733858106755281250092973 27650196790033230468784865)
  ·
    refine ⟨20737647592524922851588649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27650196790033230468784865 20737647592524922851588649)
    ·
      refine ⟨15553235694393692138691487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20737647592524922851588649 15553235694393692138691487)
      ·
        refine ⟨23329853541590538208037231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15553235694393692138691487 23329853541590538208037231)
        ·
          refine ⟨34994780312385807312055847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23329853541590538208037231 34994780312385807312055847)
          ·
            refine ⟨52492170468578710968083771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34994780312385807312055847 52492170468578710968083771)
            ·
              refine ⟨78738255702868066452125657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52492170468578710968083771 78738255702868066452125657)
              ·
                refine ⟨59053691777151049839094243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 78738255702868066452125657 59053691777151049839094243)
                ·
                  refine ⟨88580537665726574758641365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 59053691777151049839094243 88580537665726574758641365)
                  ·
                    refine ⟨2076106351540466595905657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 88580537665726574758641365 2076106351540466595905657)
                    ·
                      refine ⟨1557079763655349946929243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2076106351540466595905657 1557079763655349946929243)
                      ·
                        rfl

theorem cell23_3032402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 2, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 2, 1, 7, 2].length) (baseStart_3032402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3032402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3032402 prefixEnd_3032402 := by exact prefixLift 3032402
  have htrace : WordTrace (prefixWord ++ tailWord_3032402) baseStart_3032402 baseEnd_3032402 := by
    simpa [prefixWord, tailWord_3032402, baseEnd_3032402] using wordTrace_append hprefix tailTrace_3032402
  have hstable : (prefixWord ++ tailWord_3032402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3032402).length < 2 ^ (prefixWord ++ tailWord_3032402).sum := by decide
  have hdescent : baseEnd_3032402 < baseStart_3032402 := by decide
  rcases family_descends (prefixWord ++ tailWord_3032402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3032432 : List Nat := [2, 1, 1, 1, 4, 2, 2, 1, 1, 6, 2]
def baseStart_3032432 : Nat := 118140960795 + 3032432 * 2 ^ 59
def prefixEnd_3032432 : Nat := 4983230072969 + 3 ^ 40 * 3032432 * 2
def baseEnd_3032432 : Nat := 1557095168074984829554105

theorem tailTrace_3032432 : CollatzResearch.WordTrace tailWord_3032432 prefixEnd_3032432 1557095168074984829554105 := by
  unfold tailWord_3032432
  simp only [CollatzResearch.WordTrace]
  refine ⟨55300940675012118499365775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73734587566682824665821033 55300940675012118499365775)
  ·
    refine ⟨82951411012518177749048663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55300940675012118499365775 82951411012518177749048663)
    ·
      refine ⟨124427116518777266623572995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82951411012518177749048663 124427116518777266623572995)
      ·
        refine ⟨186640674778165899935359493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124427116518777266623572995 186640674778165899935359493)
        ·
          refine ⟨34995126520906106237879905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 186640674778165899935359493 34995126520906106237879905)
          ·
            refine ⟨26246344890679579678409929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34995126520906106237879905 26246344890679579678409929)
            ·
              refine ⟨19684758668009684758807447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26246344890679579678409929 19684758668009684758807447)
              ·
                refine ⟨29527138002014527138211171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19684758668009684758807447 29527138002014527138211171)
                ·
                  refine ⟨44290707003021790707316757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29527138002014527138211171 44290707003021790707316757)
                  ·
                    refine ⟨2076126890766646439405473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 44290707003021790707316757 2076126890766646439405473)
                    ·
                      refine ⟨1557095168074984829554105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2076126890766646439405473 1557095168074984829554105)
                      ·
                        rfl

theorem cell23_3032432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 2, 1, 1, 6, 2].length) (baseStart_3032432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3032432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3032432 prefixEnd_3032432 := by exact prefixLift 3032432
  have htrace : WordTrace (prefixWord ++ tailWord_3032432) baseStart_3032432 baseEnd_3032432 := by
    simpa [prefixWord, tailWord_3032432, baseEnd_3032432] using wordTrace_append hprefix tailTrace_3032432
  have hstable : (prefixWord ++ tailWord_3032432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3032432).length < 2 ^ (prefixWord ++ tailWord_3032432).sum := by decide
  have hdescent : baseEnd_3032432 < baseStart_3032432 := by decide
  rcases family_descends (prefixWord ++ tailWord_3032432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3032459 : List Nat := [1, 1, 1, 1, 4, 3, 2, 5, 1, 4]
def baseStart_3032459 : Nat := 118140960795 + 3032459 * 2 ^ 59
def prefixEnd_3032459 : Nat := 4983230072969 + 3 ^ 40 * 3032459 * 2
def baseEnd_3032459 : Nat := 519036344017552074638827

theorem tailTrace_3032459 : CollatzResearch.WordTrace tailWord_3032459 prefixEnd_3032459 519036344017552074638827 := by
  unfold tailWord_3032459
  simp only [CollatzResearch.WordTrace]
  refine ⟨110602866120926420609964431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73735244080617613739976287 110602866120926420609964431)
  ·
    refine ⟨165904299181389630914946647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110602866120926420609964431 165904299181389630914946647)
    ·
      refine ⟨248856448772084446372419971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165904299181389630914946647 248856448772084446372419971)
      ·
        refine ⟨373284673158126669558629957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 248856448772084446372419971 373284673158126669558629957)
        ·
          refine ⟨69990876217148750542243117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 373284673158126669558629957 69990876217148750542243117)
          ·
            refine ⟨26246578581430781453341169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 69990876217148750542243117 26246578581430781453341169)
            ·
              refine ⟨19684933936073086090005877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26246578581430781453341169 19684933936073086090005877)
              ·
                refine ⟨1845462556506851820938051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 19684933936073086090005877 1845462556506851820938051)
                ·
                  refine ⟨2768193834760277731407077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1845462556506851820938051 2768193834760277731407077)
                  ·
                    refine ⟨519036344017552074638827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2768193834760277731407077 519036344017552074638827)
                    ·
                      rfl

theorem cell23_3032459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 2, 5, 1, 4].length) (baseStart_3032459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3032459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3032459 prefixEnd_3032459 := by exact prefixLift 3032459
  have htrace : WordTrace (prefixWord ++ tailWord_3032459) baseStart_3032459 baseEnd_3032459 := by
    simpa [prefixWord, tailWord_3032459, baseEnd_3032459] using wordTrace_append hprefix tailTrace_3032459
  have hstable : (prefixWord ++ tailWord_3032459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3032459).length < 2 ^ (prefixWord ++ tailWord_3032459).sum := by decide
  have hdescent : baseEnd_3032459 < baseStart_3032459 := by decide
  rcases family_descends (prefixWord ++ tailWord_3032459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3032509 : List Nat := [1, 4, 1, 2, 2, 1, 3, 1, 1, 5, 2]
def baseStart_3032509 : Nat := 118140960795 + 3032509 * 2 ^ 59
def prefixEnd_3032509 : Nat := 4983230072969 + 3 ^ 40 * 3032509 * 2
def baseEnd_3032509 : Nat := 1557134706085381028291251

theorem tailTrace_3032509 : CollatzResearch.WordTrace tailWord_3032509 prefixEnd_3032509 1557134706085381028291251 := by
  unfold tailWord_3032509
  simp only [CollatzResearch.WordTrace]
  refine ⟨110604689770745279149284581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73736459847163519432856387 110604689770745279149284581)
  ·
    refine ⟨20738379332014739840490859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 110604689770745279149284581 20738379332014739840490859)
    ·
      refine ⟨31107568998022109760736289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20738379332014739840490859 31107568998022109760736289)
      ·
        refine ⟨23330676748516582320552217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31107568998022109760736289 23330676748516582320552217)
        ·
          refine ⟨17498007561387436740414163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23330676748516582320552217 17498007561387436740414163)
          ·
            refine ⟨26247011342081155110621245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17498007561387436740414163 26247011342081155110621245)
            ·
              refine ⟨9842629253280433166482967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26247011342081155110621245 9842629253280433166482967)
              ·
                refine ⟨14763943879920649749724451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9842629253280433166482967 14763943879920649749724451)
                ·
                  refine ⟨22145915819880974624586677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14763943879920649749724451 22145915819880974624586677)
                  ·
                    refine ⟨2076179608113841371055001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 22145915819880974624586677 2076179608113841371055001)
                    ·
                      refine ⟨1557134706085381028291251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2076179608113841371055001 1557134706085381028291251)
                      ·
                        rfl

theorem cell23_3032509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 3, 1, 1, 5, 2].length) (baseStart_3032509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3032509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3032509 prefixEnd_3032509 := by exact prefixLift 3032509
  have htrace : WordTrace (prefixWord ++ tailWord_3032509) baseStart_3032509 baseEnd_3032509 := by
    simpa [prefixWord, tailWord_3032509, baseEnd_3032509] using wordTrace_append hprefix tailTrace_3032509
  have hstable : (prefixWord ++ tailWord_3032509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3032509).length < 2 ^ (prefixWord ++ tailWord_3032509).sum := by decide
  have hdescent : baseEnd_3032509 < baseStart_3032509 := by decide
  rcases family_descends (prefixWord ++ tailWord_3032509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3032549 : List Nat := [1, 3, 1, 5, 1, 1, 3, 1, 1, 6]
def baseStart_3032549 : Nat := 118140960795 + 3032549 * 2 ^ 59
def prefixEnd_3032549 : Nat := 4983230072969 + 3 ^ 40 * 3032549 * 2
def baseEnd_3032549 : Nat := 519051748437186957263689

theorem tailTrace_3032549 : CollatzResearch.WordTrace tailWord_3032549 prefixEnd_3032549 519051748437186957263689 := by
  unfold tailWord_3032549
  simp only [CollatzResearch.WordTrace]
  refine ⟨110606148690600365980740701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73737432460400243987160467 110606148690600365980740701)
  ·
    refine ⟨41477305758975137242777763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 110606148690600365980740701 41477305758975137242777763)
    ·
      refine ⟨62215958638462705864166645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41477305758975137242777763 62215958638462705864166645)
      ·
        refine ⟨5832746122355878674765623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 62215958638462705864166645 5832746122355878674765623)
        ·
          refine ⟨8749119183533818012148435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5832746122355878674765623 8749119183533818012148435)
          ·
            refine ⟨13123678775300727018222653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8749119183533818012148435 13123678775300727018222653)
            ·
              refine ⟨4921379540737772631833495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13123678775300727018222653 4921379540737772631833495)
              ·
                refine ⟨7382069311106658947750243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4921379540737772631833495 7382069311106658947750243)
                ·
                  refine ⟨11073103966659988421625365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7382069311106658947750243 11073103966659988421625365)
                  ·
                    refine ⟨519051748437186957263689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11073103966659988421625365 519051748437186957263689)
                    ·
                      rfl

theorem cell23_3032549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 3, 1, 1, 6].length) (baseStart_3032549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3032549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3032549 prefixEnd_3032549 := by exact prefixLift 3032549
  have htrace : WordTrace (prefixWord ++ tailWord_3032549) baseStart_3032549 baseEnd_3032549 := by
    simpa [prefixWord, tailWord_3032549, baseEnd_3032549] using wordTrace_append hprefix tailTrace_3032549
  have hstable : (prefixWord ++ tailWord_3032549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3032549).length < 2 ^ (prefixWord ++ tailWord_3032549).sum := by decide
  have hdescent : baseEnd_3032549 < baseStart_3032549 := by decide
  rcases family_descends (prefixWord ++ tailWord_3032549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3032552 : List Nat := [2, 1, 4, 1, 1, 2, 3, 1, 1, 1, 6]
def baseStart_3032552 : Nat := 118140960795 + 3032552 * 2 ^ 59
def prefixEnd_3032552 : Nat := 4983230072969 + 3 ^ 40 * 3032552 * 2
def baseEnd_3032552 : Nat := 1557156785753524360053553

theorem tailTrace_3032552 : CollatzResearch.WordTrace tailWord_3032552 prefixEnd_3032552 1557156785753524360053553 := by
  unfold tailWord_3032552
  simp only [CollatzResearch.WordTrace]
  refine ⟨55303129054794748746549955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73737505406392998328733273 55303129054794748746549955)
  ·
    refine ⟨82954693582192123119824933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55303129054794748746549955 82954693582192123119824933)
    ·
      refine ⟨15554005046661023084967175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 82954693582192123119824933 15554005046661023084967175)
      ·
        refine ⟨23331007569991534627450763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15554005046661023084967175 23331007569991534627450763)
        ·
          refine ⟨34996511354987301941176145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23331007569991534627450763 34996511354987301941176145)
          ·
            refine ⟨26247383516240476455882109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34996511354987301941176145 26247383516240476455882109)
            ·
              refine ⟨9842768818590178670955791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26247383516240476455882109 9842768818590178670955791)
              ·
                refine ⟨14764153227885268006433687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9842768818590178670955791 14764153227885268006433687)
                ·
                  refine ⟨22146229841827902009650531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14764153227885268006433687 22146229841827902009650531)
                  ·
                    refine ⟨33219344762741853014475797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22146229841827902009650531 33219344762741853014475797)
                    ·
                      refine ⟨1557156785753524360053553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 33219344762741853014475797 1557156785753524360053553)
                      ·
                        rfl

theorem cell23_3032552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 3, 1, 1, 1, 6].length) (baseStart_3032552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3032552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3032552 prefixEnd_3032552 := by exact prefixLift 3032552
  have htrace : WordTrace (prefixWord ++ tailWord_3032552) baseStart_3032552 baseEnd_3032552 := by
    simpa [prefixWord, tailWord_3032552, baseEnd_3032552] using wordTrace_append hprefix tailTrace_3032552
  have hstable : (prefixWord ++ tailWord_3032552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3032552).length < 2 ^ (prefixWord ++ tailWord_3032552).sum := by decide
  have hdescent : baseEnd_3032552 < baseStart_3032552 := by decide
  rcases family_descends (prefixWord ++ tailWord_3032552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3032559 : List Nat := [1, 1, 2, 1, 4, 1, 3, 4, 1, 2, 3]
def baseStart_3032559 : Nat := 118140960795 + 3032559 * 2 ^ 59
def prefixEnd_3032559 : Nat := 4983230072969 + 3 ^ 40 * 3032559 * 2
def baseEnd_3032559 : Nat := 1557160380118105832666021

theorem tailTrace_3032559 : CollatzResearch.WordTrace tailWord_3032559 prefixEnd_3032559 1557160380118105832666021 := by
  unfold tailWord_3032559
  simp only [CollatzResearch.WordTrace]
  refine ⟨110606513420564137688604731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73737675613709425125736487 110606513420564137688604731)
  ·
    refine ⟨165909770130846206532907097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110606513420564137688604731 165909770130846206532907097)
    ·
      refine ⟨124432327598134654899680323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 165909770130846206532907097 124432327598134654899680323)
      ·
        refine ⟨186648491397201982349520485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124432327598134654899680323 186648491397201982349520485)
        ·
          refine ⟨34996592136975371690535091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 186648491397201982349520485 34996592136975371690535091)
          ·
            refine ⟨52494888205463057535802637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34996592136975371690535091 52494888205463057535802637)
            ·
              refine ⟨19685583077048646575925989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52494888205463057535802637 19685583077048646575925989)
              ·
                refine ⟨3691046826946621232986123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19685583077048646575925989 3691046826946621232986123)
                ·
                  refine ⟨5536570240419931849479185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3691046826946621232986123 5536570240419931849479185)
                  ·
                    refine ⟨4152427680314948887109389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5536570240419931849479185 4152427680314948887109389)
                    ·
                      refine ⟨1557160380118105832666021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4152427680314948887109389 1557160380118105832666021)
                      ·
                        rfl

theorem cell23_3032559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 3, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 3, 4, 1, 2, 3].length) (baseStart_3032559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3032559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3032559 prefixEnd_3032559 := by exact prefixLift 3032559
  have htrace : WordTrace (prefixWord ++ tailWord_3032559) baseStart_3032559 baseEnd_3032559 := by
    simpa [prefixWord, tailWord_3032559, baseEnd_3032559] using wordTrace_append hprefix tailTrace_3032559
  have hstable : (prefixWord ++ tailWord_3032559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3032559).length < 2 ^ (prefixWord ++ tailWord_3032559).sum := by decide
  have hdescent : baseEnd_3032559 < baseStart_3032559 := by decide
  rcases family_descends (prefixWord ++ tailWord_3032559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3032590 : List Nat := [4, 1, 1, 2, 4, 2, 1, 1, 3, 2, 2]
def baseStart_3032590 : Nat := 118140960795 + 3032590 * 2 ^ 59
def prefixEnd_3032590 : Nat := 4983230072969 + 3 ^ 40 * 3032590 * 2
def baseEnd_3032590 : Nat := 1557176298018395211378379

theorem tailTrace_3032590 : CollatzResearch.WordTrace tailWord_3032590 prefixEnd_3032590 1557176298018395211378379 := by
  unfold tailWord_3032590
  simp only [CollatzResearch.WordTrace]
  refine ⟨13825955510431478747872903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 73738429388967886655322149 13825955510431478747872903)
  ·
    refine ⟨20738933265647218121809355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13825955510431478747872903 20738933265647218121809355)
    ·
      refine ⟨31108399898470827182714033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20738933265647218121809355 31108399898470827182714033)
      ·
        refine ⟨23331299923853120387035525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31108399898470827182714033 23331299923853120387035525)
        ·
          refine ⟨4374618735722460072569161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23331299923853120387035525 4374618735722460072569161)
          ·
            refine ⟨3280964051791845054426871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4374618735722460072569161 3280964051791845054426871)
            ·
              refine ⟨4921446077687767581640307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3280964051791845054426871 4921446077687767581640307)
              ·
                refine ⟨7382169116531651372460461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4921446077687767581640307 7382169116531651372460461)
                ·
                  refine ⟨2768313418699369264672673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7382169116531651372460461 2768313418699369264672673)
                  ·
                    refine ⟨2076235064024526948504505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2768313418699369264672673 2076235064024526948504505)
                    ·
                      refine ⟨1557176298018395211378379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2076235064024526948504505 1557176298018395211378379)
                      ·
                        rfl

theorem cell23_3032590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 2, 1, 1, 3, 2, 2].length) (baseStart_3032590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3032590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3032590 prefixEnd_3032590 := by exact prefixLift 3032590
  have htrace : WordTrace (prefixWord ++ tailWord_3032590) baseStart_3032590 baseEnd_3032590 := by
    simpa [prefixWord, tailWord_3032590, baseEnd_3032590] using wordTrace_append hprefix tailTrace_3032590
  have hstable : (prefixWord ++ tailWord_3032590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3032590).length < 2 ^ (prefixWord ++ tailWord_3032590).sum := by decide
  have hdescent : baseEnd_3032590 < baseStart_3032590 := by decide
  rcases family_descends (prefixWord ++ tailWord_3032590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3032596 : List Nat := [2, 4, 3, 1, 2, 1, 2, 8]
def baseStart_3032596 : Nat := 118140960795 + 3032596 * 2 ^ 59
def prefixEnd_3032596 : Nat := 4983230072969 + 3 ^ 40 * 3032596 * 2
def baseEnd_3032596 : Nat := 57673310329715636589013

theorem tailTrace_3032596 : CollatzResearch.WordTrace tailWord_3032596 prefixEnd_3032596 57673310329715636589013 := by
  unfold tailWord_3032596
  simp only [CollatzResearch.WordTrace]
  refine ⟨55303931460715046503850821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73738575280953395338467761 55303931460715046503850821)
  ·
    refine ⟨10369487148884071219472029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 55303931460715046503850821 10369487148884071219472029)
    ·
      refine ⟨3888557680831526707302011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10369487148884071219472029 3888557680831526707302011)
      ·
        refine ⟨5832836521247290060953017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3888557680831526707302011 5832836521247290060953017)
        ·
          refine ⟨4374627390935467545714763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5832836521247290060953017 4374627390935467545714763)
          ·
            refine ⟨6561941086403201318572145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4374627390935467545714763 6561941086403201318572145)
            ·
              refine ⟨4921455814802400988929109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6561941086403201318572145 4921455814802400988929109)
              ·
                refine ⟨57673310329715636589013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4921455814802400988929109 57673310329715636589013)
                ·
                  rfl

theorem cell23_3032596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 2, 8].length) (baseStart_3032596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3032596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3032596 prefixEnd_3032596 := by exact prefixLift 3032596
  have htrace : WordTrace (prefixWord ++ tailWord_3032596) baseStart_3032596 baseEnd_3032596 := by
    simpa [prefixWord, tailWord_3032596, baseEnd_3032596] using wordTrace_append hprefix tailTrace_3032596
  have hstable : (prefixWord ++ tailWord_3032596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3032596).length < 2 ^ (prefixWord ++ tailWord_3032596).sum := by decide
  have hdescent : baseEnd_3032596 < baseStart_3032596 := by decide
  rcases family_descends (prefixWord ++ tailWord_3032596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3032600 : List Nat := [2, 1, 2, 3, 5, 1, 2, 1, 2, 4]
def baseStart_3032600 : Nat := 118140960795 + 3032600 * 2 ^ 59
def prefixEnd_3032600 : Nat := 4983230072969 + 3 ^ 40 * 3032600 * 2
def baseEnd_3032600 : Nat := 519060477608313390751111

theorem tailTrace_3032600 : CollatzResearch.WordTrace tailWord_3032600 prefixEnd_3032600 519060477608313390751111 := by
  unfold tailWord_3032600
  simp only [CollatzResearch.WordTrace]
  refine ⟨55304004406707800845423627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73738672542277067793898169 55304004406707800845423627)
  ·
    refine ⟨82956006610061701268135441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55304004406707800845423627 82956006610061701268135441)
    ·
      refine ⟨62217004957546275951101581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82956006610061701268135441 62217004957546275951101581)
      ·
        refine ⟨23331376859079853481663093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62217004957546275951101581 23331376859079853481663093)
        ·
          refine ⟨2187316580538736263905915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 23331376859079853481663093 2187316580538736263905915)
          ·
            refine ⟨3280974870808104395858873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2187316580538736263905915 3280974870808104395858873)
            ·
              refine ⟨2460731153106078296894155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3280974870808104395858873 2460731153106078296894155)
              ·
                refine ⟨3691096729659117445341233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2460731153106078296894155 3691096729659117445341233)
                ·
                  refine ⟨2768322547244338084005925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3691096729659117445341233 2768322547244338084005925)
                  ·
                    refine ⟨519060477608313390751111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2768322547244338084005925 519060477608313390751111)
                    ·
                      rfl

theorem cell23_3032600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 5, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 5, 1, 2, 1, 2, 4].length) (baseStart_3032600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3032600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3032600 prefixEnd_3032600 := by exact prefixLift 3032600
  have htrace : WordTrace (prefixWord ++ tailWord_3032600) baseStart_3032600 baseEnd_3032600 := by
    simpa [prefixWord, tailWord_3032600, baseEnd_3032600] using wordTrace_append hprefix tailTrace_3032600
  have hstable : (prefixWord ++ tailWord_3032600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3032600).length < 2 ^ (prefixWord ++ tailWord_3032600).sum := by decide
  have hdescent : baseEnd_3032600 < baseStart_3032600 := by decide
  rcases family_descends (prefixWord ++ tailWord_3032600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3032663 : List Nat := [1, 1, 3, 2, 2, 3, 2, 3, 2, 2, 2]
def baseStart_3032663 : Nat := 118140960795 + 3032663 * 2 ^ 59
def prefixEnd_3032663 : Nat := 4983230072969 + 3 ^ 40 * 3032663 * 2
def baseEnd_3032663 : Nat := 1557213782106173425765543

theorem tailTrace_3032663 : CollatzResearch.WordTrace tailWord_3032663 prefixEnd_3032663 1557213782106173425765543 := by
  unfold tailWord_3032663
  simp only [CollatzResearch.WordTrace]
  refine ⟨110610306612187363450390643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73740204408124908966927095 110610306612187363450390643)
  ·
    refine ⟨165915459918281045175585965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110610306612187363450390643 165915459918281045175585965)
    ·
      refine ⟨62218297469355391940844737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 165915459918281045175585965 62218297469355391940844737)
      ·
        refine ⟨46663723102016543955633553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62218297469355391940844737 46663723102016543955633553)
        ·
          refine ⟨34997792326512407966725165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46663723102016543955633553 34997792326512407966725165)
          ·
            refine ⟨13124172122442152987521937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34997792326512407966725165 13124172122442152987521937)
            ·
              refine ⟨9843129091831614740641453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13124172122442152987521937 9843129091831614740641453)
              ·
                refine ⟨3691173409436855527740545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9843129091831614740641453 3691173409436855527740545)
                ·
                  refine ⟨2768380057077641645805409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3691173409436855527740545 2768380057077641645805409)
                  ·
                    refine ⟨2076285042808231234354057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2768380057077641645805409 2076285042808231234354057)
                    ·
                      refine ⟨1557213782106173425765543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2076285042808231234354057 1557213782106173425765543)
                      ·
                        rfl

theorem cell23_3032663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 2, 3, 2, 2, 2].length) (baseStart_3032663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3032663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3032663 prefixEnd_3032663 := by exact prefixLift 3032663
  have htrace : WordTrace (prefixWord ++ tailWord_3032663) baseStart_3032663 baseEnd_3032663 := by
    simpa [prefixWord, tailWord_3032663, baseEnd_3032663] using wordTrace_append hprefix tailTrace_3032663
  have hstable : (prefixWord ++ tailWord_3032663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3032663).length < 2 ^ (prefixWord ++ tailWord_3032663).sum := by decide
  have hdescent : baseEnd_3032663 < baseStart_3032663 := by decide
  rcases family_descends (prefixWord ++ tailWord_3032663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3032729 : List Nat := [1, 2, 1, 2, 1, 2, 2, 3, 5, 4]
def baseStart_3032729 : Nat := 118140960795 + 3032729 * 2 ^ 59
def prefixEnd_3032729 : Nat := 4983230072969 + 3 ^ 40 * 3032729 * 2
def baseEnd_3032729 : Nat := 519082557276456722513413

theorem tailTrace_3032729 : CollatzResearch.WordTrace tailWord_3032729 prefixEnd_3032729 519082557276456722513413 := by
  unfold tailWord_3032729
  simp only [CollatzResearch.WordTrace]
  refine ⟨110612713829948256722293241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73741809219965504481528827 110612713829948256722293241)
  ·
    refine ⟨82959535372461192541719931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110612713829948256722293241 82959535372461192541719931)
    ·
      refine ⟨124439303058691788812579897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82959535372461192541719931 124439303058691788812579897)
      ·
        refine ⟨93329477294018841609434923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 124439303058691788812579897 93329477294018841609434923)
        ·
          refine ⟨139994215941028262414152385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93329477294018841609434923 139994215941028262414152385)
          ·
            refine ⟨104995661955771196810614289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 139994215941028262414152385 104995661955771196810614289)
            ·
              refine ⟨78746746466828397607960717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 104995661955771196810614289 78746746466828397607960717)
              ·
                refine ⟨29530029925060649102985269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 78746746466828397607960717 29530029925060649102985269)
                ·
                  refine ⟨2768440305474435853404869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 29530029925060649102985269 2768440305474435853404869)
                  ·
                    refine ⟨519082557276456722513413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2768440305474435853404869 519082557276456722513413)
                    ·
                      rfl

theorem cell23_3032729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 3, 5, 4].length) (baseStart_3032729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3032729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3032729 prefixEnd_3032729 := by exact prefixLift 3032729
  have htrace : WordTrace (prefixWord ++ tailWord_3032729) baseStart_3032729 baseEnd_3032729 := by
    simpa [prefixWord, tailWord_3032729, baseEnd_3032729] using wordTrace_append hprefix tailTrace_3032729
  have hstable : (prefixWord ++ tailWord_3032729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3032729).length < 2 ^ (prefixWord ++ tailWord_3032729).sum := by decide
  have hdescent : baseEnd_3032729 < baseStart_3032729 := by decide
  rcases family_descends (prefixWord ++ tailWord_3032729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3032739 : List Nat := [1, 1, 1, 4, 1, 1, 3, 3, 1, 4, 3]
def baseStart_3032739 : Nat := 118140960795 + 3032739 * 2 ^ 59
def prefixEnd_3032739 : Nat := 4983230072969 + 3 ^ 40 * 3032739 * 2
def baseEnd_3032739 : Nat := 1557252806635915128415193

theorem tailTrace_3032739 : CollatzResearch.WordTrace tailWord_3032739 prefixEnd_3032739 1557252806635915128415193 := by
  unfold tailWord_3032739
  simp only [CollatzResearch.WordTrace]
  refine ⟨110613078559912028430157271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73742052373274685620104847 110613078559912028430157271)
  ·
    refine ⟨165919617839868042645235907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110613078559912028430157271 165919617839868042645235907)
    ·
      refine ⟨248879426759802063967853861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165919617839868042645235907 248879426759802063967853861)
      ·
        refine ⟨46664892517462886993972599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 248879426759802063967853861 46664892517462886993972599)
        ·
          refine ⟨69997338776194330490958899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46664892517462886993972599 69997338776194330490958899)
          ·
            refine ⟨104996008164291495736438349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69997338776194330490958899 104996008164291495736438349)
            ·
              refine ⟨39373503061609310901164381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 104996008164291495736438349 39373503061609310901164381)
              ·
                refine ⟨14765063648103491587936643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39373503061609310901164381 14765063648103491587936643)
                ·
                  refine ⟨22147595472155237381904965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14765063648103491587936643 22147595472155237381904965)
                  ·
                    refine ⟨4152674151029107009107181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22147595472155237381904965 4152674151029107009107181)
                    ·
                      refine ⟨1557252806635915128415193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4152674151029107009107181 1557252806635915128415193)
                      ·
                        rfl

theorem cell23_3032739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 3, 1, 4, 3].length) (baseStart_3032739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3032739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3032739 prefixEnd_3032739 := by exact prefixLift 3032739
  have htrace : WordTrace (prefixWord ++ tailWord_3032739) baseStart_3032739 baseEnd_3032739 := by
    simpa [prefixWord, tailWord_3032739, baseEnd_3032739] using wordTrace_append hprefix tailTrace_3032739
  have hstable : (prefixWord ++ tailWord_3032739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3032739).length < 2 ^ (prefixWord ++ tailWord_3032739).sum := by decide
  have hdescent : baseEnd_3032739 < baseStart_3032739 := by decide
  rcases family_descends (prefixWord ++ tailWord_3032739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3032759 : List Nat := [1, 1, 3, 1, 5, 1, 2, 1, 8]
def baseStart_3032759 : Nat := 118140960795 + 3032759 * 2 ^ 59
def prefixEnd_3032759 : Nat := 4983230072969 + 3 ^ 40 * 3032759 * 2
def baseEnd_3032759 : Nat := 173029230694333894462789

theorem tailTrace_3032759 : CollatzResearch.WordTrace tailWord_3032759 prefixEnd_3032759 173029230694333894462789 := by
  unfold tailWord_3032759
  simp only [CollatzResearch.WordTrace]
  refine ⟨110613808019839571845885331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73742538679893047897256887 110613808019839571845885331)
  ·
    refine ⟨165920712029759357768827997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110613808019839571845885331 165920712029759357768827997)
    ·
      refine ⟨62220267011159759163310499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 165920712029759357768827997 62220267011159759163310499)
      ·
        refine ⟨93330400516739638744965749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62220267011159759163310499 93330400516739638744965749)
        ·
          refine ⟨8749725048444341132340539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 93330400516739638744965749 8749725048444341132340539)
          ·
            refine ⟨13124587572666511698510809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8749725048444341132340539 13124587572666511698510809)
            ·
              refine ⟨9843440679499883773883107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13124587572666511698510809 9843440679499883773883107)
              ·
                refine ⟨14765161019249825660824661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9843440679499883773883107 14765161019249825660824661)
                ·
                  refine ⟨173029230694333894462789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 14765161019249825660824661 173029230694333894462789)
                  ·
                    rfl

theorem cell23_3032759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 2, 1, 8].length) (baseStart_3032759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3032759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3032759 prefixEnd_3032759 := by exact prefixLift 3032759
  have htrace : WordTrace (prefixWord ++ tailWord_3032759) baseStart_3032759 baseEnd_3032759 := by
    simpa [prefixWord, tailWord_3032759, baseEnd_3032759] using wordTrace_append hprefix tailTrace_3032759
  have hstable : (prefixWord ++ tailWord_3032759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3032759).length < 2 ^ (prefixWord ++ tailWord_3032759).sum := by decide
  have hdescent : baseEnd_3032759 < baseStart_3032759 := by decide
  rcases family_descends (prefixWord ++ tailWord_3032759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3032826 : List Nat := [3, 1, 1, 1, 1, 3, 1, 2, 2, 6, 2]
def baseStart_3032826 : Nat := 118140960795 + 3032826 * 2 ^ 59
def prefixEnd_3032826 : Nat := 4983230072969 + 3 ^ 40 * 3032826 * 2
def baseEnd_3032826 : Nat := 1557297479452856288027293

theorem tailTrace_3032826 : CollatzResearch.WordTrace tailWord_3032826 prefixEnd_3032826 1557297479452856288027293 := by
  unfold tailWord_3032826
  simp only [CollatzResearch.WordTrace]
  refine ⟨27654062927649210572143583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73744167807064561525716221 27654062927649210572143583)
  ·
    refine ⟨41481094391473815858215375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27654062927649210572143583 41481094391473815858215375)
    ·
      refine ⟨62221641587210723787323063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41481094391473815858215375 62221641587210723787323063)
      ·
        refine ⟨93332462380816085680984595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62221641587210723787323063 93332462380816085680984595)
        ·
          refine ⟨139998693571224128521476893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93332462380816085680984595 139998693571224128521476893)
          ·
            refine ⟨52499510089209048195553835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 139998693571224128521476893 52499510089209048195553835)
            ·
              refine ⟨78749265133813572293330753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52499510089209048195553835 78749265133813572293330753)
              ·
                refine ⟨59061948850360179219998065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 78749265133813572293330753 59061948850360179219998065)
                ·
                  refine ⟨44296461637770134414998549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 59061948850360179219998065 44296461637770134414998549)
                  ·
                    refine ⟨2076396639270475050703057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 44296461637770134414998549 2076396639270475050703057)
                    ·
                      refine ⟨1557297479452856288027293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2076396639270475050703057 1557297479452856288027293)
                      ·
                        rfl

theorem cell23_3032826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 2, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 2, 2, 6, 2].length) (baseStart_3032826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3032826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3032826 prefixEnd_3032826 := by exact prefixLift 3032826
  have htrace : WordTrace (prefixWord ++ tailWord_3032826) baseStart_3032826 baseEnd_3032826 := by
    simpa [prefixWord, tailWord_3032826, baseEnd_3032826] using wordTrace_append hprefix tailTrace_3032826
  have hstable : (prefixWord ++ tailWord_3032826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3032826).length < 2 ^ (prefixWord ++ tailWord_3032826).sum := by decide
  have hdescent : baseEnd_3032826 < baseStart_3032826 := by decide
  rcases family_descends (prefixWord ++ tailWord_3032826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3032836 : List Nat := [2, 3, 2, 2, 1, 2, 1, 3, 1, 6]
def baseStart_3032836 : Nat := 118140960795 + 3032836 * 2 ^ 59
def prefixEnd_3032836 : Nat := 4983230072969 + 3 ^ 40 * 3032836 * 2
def baseEnd_3032836 : Nat := 519100871419800416300749

theorem tailTrace_3032836 : CollatzResearch.WordTrace tailWord_3032836 prefixEnd_3032836 519100871419800416300749 := by
  unfold tailWord_3032836
  simp only [CollatzResearch.WordTrace]
  refine ⟨55308308220280306998219181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73744410960373742664292241 55308308220280306998219181)
  ·
    refine ⟨20740615582605115124332193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55308308220280306998219181 20740615582605115124332193)
    ·
      refine ⟨15555461686953836343249145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20740615582605115124332193 15555461686953836343249145)
      ·
        refine ⟨11666596265215377257436859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15555461686953836343249145 11666596265215377257436859)
        ·
          refine ⟨17499894397823065886155289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11666596265215377257436859 17499894397823065886155289)
          ·
            refine ⟨13124920798367299414616467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17499894397823065886155289 13124920798367299414616467)
            ·
              refine ⟨19687381197550949121924701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13124920798367299414616467 19687381197550949121924701)
              ·
                refine ⟨7382767949081605920721763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19687381197550949121924701 7382767949081605920721763)
                ·
                  refine ⟨11074151923622408881082645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7382767949081605920721763 11074151923622408881082645)
                  ·
                    refine ⟨519100871419800416300749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11074151923622408881082645 519100871419800416300749)
                    ·
                      rfl

theorem cell23_3032836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 1, 3, 1, 6].length) (baseStart_3032836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3032836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3032836 prefixEnd_3032836 := by exact prefixLift 3032836
  have htrace : WordTrace (prefixWord ++ tailWord_3032836) baseStart_3032836 baseEnd_3032836 := by
    simpa [prefixWord, tailWord_3032836, baseEnd_3032836] using wordTrace_append hprefix tailTrace_3032836
  have hstable : (prefixWord ++ tailWord_3032836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3032836).length < 2 ^ (prefixWord ++ tailWord_3032836).sum := by decide
  have hdescent : baseEnd_3032836 < baseStart_3032836 := by decide
  rcases family_descends (prefixWord ++ tailWord_3032836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3032838 : List Nat := [6, 2, 2, 1, 2, 1, 1, 1, 2, 1, 4]
def baseStart_3032838 : Nat := 118140960795 + 3032838 * 2 ^ 59
def prefixEnd_3032838 : Nat := 4983230072969 + 3 ^ 40 * 3032838 * 2
def baseEnd_3032838 : Nat := 1557303641220710241077239

theorem tailTrace_3032838 : CollatzResearch.WordTrace tailWord_3032838 prefixEnd_3032838 1557303641220710241077239 := by
  unfold tailWord_3032838
  simp only [CollatzResearch.WordTrace]
  refine ⟨3456771543329792760562849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 73744459591035578892007445 3456771543329792760562849)
  ·
    refine ⟨2592578657497344570422137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3456771543329792760562849 2592578657497344570422137)
    ·
      refine ⟨1944433993123008427816603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2592578657497344570422137 1944433993123008427816603)
      ·
        refine ⟨2916650989684512641724905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1944433993123008427816603 2916650989684512641724905)
        ·
          refine ⟨2187488242263384481293679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2916650989684512641724905 2187488242263384481293679)
          ·
            refine ⟨3281232363395076721940519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2187488242263384481293679 3281232363395076721940519)
            ·
              refine ⟨4921848545092615082910779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3281232363395076721940519 4921848545092615082910779)
              ·
                refine ⟨7382772817638922624366169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4921848545092615082910779 7382772817638922624366169)
                ·
                  refine ⟨5537079613229191968274627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7382772817638922624366169 5537079613229191968274627)
                  ·
                    refine ⟨8305619419843787952411941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5537079613229191968274627 8305619419843787952411941)
                    ·
                      refine ⟨1557303641220710241077239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8305619419843787952411941 1557303641220710241077239)
                      ·
                        rfl

theorem cell23_3032838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 2, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 2, 1, 1, 1, 2, 1, 4].length) (baseStart_3032838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3032838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3032838 prefixEnd_3032838 := by exact prefixLift 3032838
  have htrace : WordTrace (prefixWord ++ tailWord_3032838) baseStart_3032838 baseEnd_3032838 := by
    simpa [prefixWord, tailWord_3032838, baseEnd_3032838] using wordTrace_append hprefix tailTrace_3032838
  have hstable : (prefixWord ++ tailWord_3032838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3032838).length < 2 ^ (prefixWord ++ tailWord_3032838).sum := by decide
  have hdescent : baseEnd_3032838 < baseStart_3032838 := by decide
  rcases family_descends (prefixWord ++ tailWord_3032838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3032843 : List Nat := [1, 1, 1, 1, 5, 1, 3, 1, 5, 2, 2]
def baseStart_3032843 : Nat := 118140960795 + 3032843 * 2 ^ 59
def prefixEnd_3032843 : Nat := 4983230072969 + 3 ^ 40 * 3032843 * 2
def baseEnd_3032843 : Nat := 1557306208623982721514715

theorem tailTrace_3032843 : CollatzResearch.WordTrace tailWord_3032843 prefixEnd_3032843 1557306208623982721514715 := by
  unfold tailWord_3032843
  simp only [CollatzResearch.WordTrace]
  refine ⟨110616871751535254191943183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73744581167690169461295455 110616871751535254191943183)
  ·
    refine ⟨165925307627302881287914775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110616871751535254191943183 165925307627302881287914775)
    ·
      refine ⟨248887961440954321931872163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165925307627302881287914775 248887961440954321931872163)
      ·
        refine ⟨373331942161431482897808245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 248887961440954321931872163 373331942161431482897808245)
        ·
          refine ⟨34999869577634201521669523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 373331942161431482897808245 34999869577634201521669523)
          ·
            refine ⟨52499804366451302282504285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34999869577634201521669523 52499804366451302282504285)
            ·
              refine ⟨19687426637419238355939107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52499804366451302282504285 19687426637419238355939107)
              ·
                refine ⟨29531139956128857533908661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19687426637419238355939107 29531139956128857533908661)
                ·
                  refine ⟨2768544370887080393803937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 29531139956128857533908661 2768544370887080393803937)
                  ·
                    refine ⟨2076408278165310295352953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2768544370887080393803937 2076408278165310295352953)
                    ·
                      refine ⟨1557306208623982721514715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2076408278165310295352953 1557306208623982721514715)
                      ·
                        rfl

theorem cell23_3032843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 3, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 3, 1, 5, 2, 2].length) (baseStart_3032843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3032843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3032843 prefixEnd_3032843 := by exact prefixLift 3032843
  have htrace : WordTrace (prefixWord ++ tailWord_3032843) baseStart_3032843 baseEnd_3032843 := by
    simpa [prefixWord, tailWord_3032843, baseEnd_3032843] using wordTrace_append hprefix tailTrace_3032843
  have hstable : (prefixWord ++ tailWord_3032843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3032843).length < 2 ^ (prefixWord ++ tailWord_3032843).sum := by decide
  have hdescent : baseEnd_3032843 < baseStart_3032843 := by decide
  rcases family_descends (prefixWord ++ tailWord_3032843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3032856 : List Nat := [2, 1, 2, 3, 1, 1, 4, 2, 1, 2, 4]
def baseStart_3032856 : Nat := 118140960795 + 3032856 * 2 ^ 59
def prefixEnd_3032856 : Nat := 4983230072969 + 3 ^ 40 * 3032856 * 2
def baseEnd_3032856 : Nat := 1557312883872491170652155

theorem tailTrace_3032856 : CollatzResearch.WordTrace tailWord_3032856 prefixEnd_3032856 1557312883872491170652155 := by
  unfold tailWord_3032856
  simp only [CollatzResearch.WordTrace]
  refine ⟨55308672950244078706083211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73744897266992104941444281 55308672950244078706083211)
  ·
    refine ⟨82963009425366118059124817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55308672950244078706083211 82963009425366118059124817)
    ·
      refine ⟨62222257069024588544343613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82963009425366118059124817 62222257069024588544343613)
      ·
        refine ⟨23333346400884220704128855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62222257069024588544343613 23333346400884220704128855)
        ·
          refine ⟨35000019601326331056193283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23333346400884220704128855 35000019601326331056193283)
          ·
            refine ⟨52500029401989496584289925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35000019601326331056193283 52500029401989496584289925)
            ·
              refine ⟨9843755512873030609554361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 52500029401989496584289925 9843755512873030609554361)
              ·
                refine ⟨7382816634654772957165771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9843755512873030609554361 7382816634654772957165771)
                ·
                  refine ⟨11074224951982159435748657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7382816634654772957165771 11074224951982159435748657)
                  ·
                    refine ⟨8305668713986619576811493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11074224951982159435748657 8305668713986619576811493)
                    ·
                      refine ⟨1557312883872491170652155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8305668713986619576811493 1557312883872491170652155)
                      ·
                        rfl

theorem cell23_3032856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 4, 2, 1, 2, 4].length) (baseStart_3032856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3032856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3032856 prefixEnd_3032856 := by exact prefixLift 3032856
  have htrace : WordTrace (prefixWord ++ tailWord_3032856) baseStart_3032856 baseEnd_3032856 := by
    simpa [prefixWord, tailWord_3032856, baseEnd_3032856] using wordTrace_append hprefix tailTrace_3032856
  have hstable : (prefixWord ++ tailWord_3032856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3032856).length < 2 ^ (prefixWord ++ tailWord_3032856).sum := by decide
  have hdescent : baseEnd_3032856 < baseStart_3032856 := by decide
  rcases family_descends (prefixWord ++ tailWord_3032856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3032863 : List Nat := [1, 1, 2, 4, 2, 1, 3, 3, 1, 2, 3]
def baseStart_3032863 : Nat := 118140960795 + 3032863 * 2 ^ 59
def prefixEnd_3032863 : Nat := 4983230072969 + 3 ^ 40 * 3032863 * 2
def baseEnd_3032863 : Nat := 1557316478237072643264623

theorem tailTrace_3032863 : CollatzResearch.WordTrace tailWord_3032863 prefixEnd_3032863 1557316478237072643264623 := by
  unfold tailWord_3032863
  simp only [CollatzResearch.WordTrace]
  refine ⟨110617601211462797607671243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73745067474308531738447495 110617601211462797607671243)
  ·
    refine ⟨165926401817194196411506865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110617601211462797607671243 165926401817194196411506865)
    ·
      refine ⟨124444801362895647308630149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 165926401817194196411506865 124444801362895647308630149)
      ·
        refine ⟨23333400255542933870368153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 124444801362895647308630149 23333400255542933870368153)
        ·
          refine ⟨17500050191657200402776115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23333400255542933870368153 17500050191657200402776115)
          ·
            refine ⟨26250075287485800604164173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17500050191657200402776115 26250075287485800604164173)
            ·
              refine ⟨9843778232807175226561565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26250075287485800604164173 9843778232807175226561565)
              ·
                refine ⟨3691416837302690709960587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9843778232807175226561565 3691416837302690709960587)
                ·
                  refine ⟨5537125255954036064940881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3691416837302690709960587 5537125255954036064940881)
                  ·
                    refine ⟨4152843941965527048705661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5537125255954036064940881 4152843941965527048705661)
                    ·
                      refine ⟨1557316478237072643264623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4152843941965527048705661 1557316478237072643264623)
                      ·
                        rfl

theorem cell23_3032863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 3, 3, 1, 2, 3].length) (baseStart_3032863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3032863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3032863 prefixEnd_3032863 := by exact prefixLift 3032863
  have htrace : WordTrace (prefixWord ++ tailWord_3032863) baseStart_3032863 baseEnd_3032863 := by
    simpa [prefixWord, tailWord_3032863, baseEnd_3032863] using wordTrace_append hprefix tailTrace_3032863
  have hstable : (prefixWord ++ tailWord_3032863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3032863).length < 2 ^ (prefixWord ++ tailWord_3032863).sum := by decide
  have hdescent : baseEnd_3032863 < baseStart_3032863 := by decide
  rcases family_descends (prefixWord ++ tailWord_3032863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3032903 : List Nat := [1, 1, 4, 1, 2, 1, 2, 3, 3, 3, 2]
def baseStart_3032903 : Nat := 118140960795 + 3032903 * 2 ^ 59
def prefixEnd_3032903 : Nat := 4983230072969 + 3 ^ 40 * 3032903 * 2
def baseEnd_3032903 : Nat := 1557337017463252486764439

theorem tailTrace_3032903 : CollatzResearch.WordTrace tailWord_3032903 prefixEnd_3032903 1557337017463252486764439 := by
  unfold tailWord_3032903
  simp only [CollatzResearch.WordTrace]
  refine ⟨110619060131317884439127363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73746040087545256292751575 110619060131317884439127363)
  ·
    refine ⟨165928590196976826658691045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110619060131317884439127363 165928590196976826658691045)
    ·
      refine ⟨31111610661933154998504571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 165928590196976826658691045 31111610661933154998504571)
      ·
        refine ⟨46667415992899732497756857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31111610661933154998504571 46667415992899732497756857)
        ·
          refine ⟨35000561994674799373317643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46667415992899732497756857 35000561994674799373317643)
          ·
            refine ⟨52500842992012199059976465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35000561994674799373317643 52500842992012199059976465)
            ·
              refine ⟨39375632244009149294982349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52500842992012199059976465 39375632244009149294982349)
              ·
                refine ⟨14765862091503430985618381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39375632244009149294982349 14765862091503430985618381)
                ·
                  refine ⟨5537198284313786619606893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14765862091503430985618381 5537198284313786619606893)
                  ·
                    refine ⟨2076449356617669982352585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5537198284313786619606893 2076449356617669982352585)
                    ·
                      refine ⟨1557337017463252486764439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2076449356617669982352585 1557337017463252486764439)
                      ·
                        rfl

theorem cell23_3032903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 3, 3, 3, 2].length) (baseStart_3032903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3032903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3032903 prefixEnd_3032903 := by exact prefixLift 3032903
  have htrace : WordTrace (prefixWord ++ tailWord_3032903) baseStart_3032903 baseEnd_3032903 := by
    simpa [prefixWord, tailWord_3032903, baseEnd_3032903] using wordTrace_append hprefix tailTrace_3032903
  have hstable : (prefixWord ++ tailWord_3032903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3032903).length < 2 ^ (prefixWord ++ tailWord_3032903).sum := by decide
  have hdescent : baseEnd_3032903 < baseStart_3032903 := by decide
  rcases family_descends (prefixWord ++ tailWord_3032903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3032936 : List Nat := [2, 1, 4, 2, 1, 1, 1, 2, 1, 3, 5]
def baseStart_3032936 : Nat := 118140960795 + 3032936 * 2 ^ 59
def prefixEnd_3032936 : Nat := 4983230072969 + 3 ^ 40 * 3032936 * 2
def baseEnd_3032936 : Nat := 1557353962324850857651787

theorem tailTrace_3032936 : CollatzResearch.WordTrace tailWord_3032936 prefixEnd_3032936 1557353962324850857651787 := by
  unfold tailWord_3032936
  simp only [CollatzResearch.WordTrace]
  refine ⟨55310131870099165537539331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73746842493465554050052441 55310131870099165537539331)
  ·
    refine ⟨82965197805148748306308997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55310131870099165537539331 82965197805148748306308997)
    ·
      refine ⟨15555974588465390307432937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 82965197805148748306308997 15555974588465390307432937)
      ·
        refine ⟨11666980941349042730574703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15555974588465390307432937 11666980941349042730574703)
        ·
          refine ⟨17500471412023564095862055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11666980941349042730574703 17500471412023564095862055)
          ·
            refine ⟨26250707118035346143793083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17500471412023564095862055 26250707118035346143793083)
            ·
              refine ⟨39376060677053019215689625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26250707118035346143793083 39376060677053019215689625)
              ·
                refine ⟨29532045507789764411767219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39376060677053019215689625 29532045507789764411767219)
                ·
                  refine ⟨44298068261684646617650829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29532045507789764411767219 44298068261684646617650829)
                  ·
                    refine ⟨16611775598131742481619061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 44298068261684646617650829 16611775598131742481619061)
                    ·
                      refine ⟨1557353962324850857651787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16611775598131742481619061 1557353962324850857651787)
                      ·
                        rfl

theorem cell23_3032936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 2, 1, 3, 5].length) (baseStart_3032936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3032936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3032936 prefixEnd_3032936 := by exact prefixLift 3032936
  have htrace : WordTrace (prefixWord ++ tailWord_3032936) baseStart_3032936 baseEnd_3032936 := by
    simpa [prefixWord, tailWord_3032936, baseEnd_3032936] using wordTrace_append hprefix tailTrace_3032936
  have hstable : (prefixWord ++ tailWord_3032936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3032936).length < 2 ^ (prefixWord ++ tailWord_3032936).sum := by decide
  have hdescent : baseEnd_3032936 < baseStart_3032936 := by decide
  rcases family_descends (prefixWord ++ tailWord_3032936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3032946 : List Nat := [3, 2, 1, 2, 1, 1, 1, 3, 1, 4, 4]
def baseStart_3032946 : Nat := 118140960795 + 3032946 * 2 ^ 59
def prefixEnd_3032946 : Nat := 4983230072969 + 3 ^ 40 * 3032946 * 2
def baseEnd_3032946 : Nat := 1557359097131395818526741

theorem tailTrace_3032946 : CollatzResearch.WordTrace tailWord_3032946 prefixEnd_3032946 1557359097131395818526741 := by
  unfold tailWord_3032946
  simp only [CollatzResearch.WordTrace]
  refine ⟨27655157117540525695735673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73747085646774735188628461 27655157117540525695735673)
  ·
    refine ⟨20741367838155394271801755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27655157117540525695735673 20741367838155394271801755)
    ·
      refine ⟨31112051757233091407702633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20741367838155394271801755 31112051757233091407702633)
      ·
        refine ⟨23334038817924818555776975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31112051757233091407702633 23334038817924818555776975)
        ·
          refine ⟨35001058226887227833665463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23334038817924818555776975 35001058226887227833665463)
          ·
            refine ⟨52501587340330841750498195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35001058226887227833665463 52501587340330841750498195)
            ·
              refine ⟨78752381010496262625747293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52501587340330841750498195 78752381010496262625747293)
              ·
                refine ⟨29532142878936098484655235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 78752381010496262625747293 29532142878936098484655235)
                ·
                  refine ⟨44298214318404147726982853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29532142878936098484655235 44298214318404147726982853)
                  ·
                    refine ⟨8305915184700777698809285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 44298214318404147726982853 8305915184700777698809285)
                    ·
                      refine ⟨1557359097131395818526741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8305915184700777698809285 1557359097131395818526741)
                      ·
                        rfl

theorem cell23_3032946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 3, 1, 4, 4].length) (baseStart_3032946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3032946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3032946 prefixEnd_3032946 := by exact prefixLift 3032946
  have htrace : WordTrace (prefixWord ++ tailWord_3032946) baseStart_3032946 baseEnd_3032946 := by
    simpa [prefixWord, tailWord_3032946, baseEnd_3032946] using wordTrace_append hprefix tailTrace_3032946
  have hstable : (prefixWord ++ tailWord_3032946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3032946).length < 2 ^ (prefixWord ++ tailWord_3032946).sum := by decide
  have hdescent : baseEnd_3032946 < baseStart_3032946 := by decide
  rcases family_descends (prefixWord ++ tailWord_3032946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3033020 : List Nat := [2, 2, 2, 5, 1, 1, 1, 1, 1, 7]
def baseStart_3033020 : Nat := 118140960795 + 3033020 * 2 ^ 59
def prefixEnd_3033020 : Nat := 4983230072969 + 3 ^ 40 * 3033020 * 2
def baseEnd_3033020 : Nat := 519132364899942843000467

theorem tailTrace_3033020 : CollatzResearch.WordTrace tailWord_3033020 prefixEnd_3033020 519132364899942843000467 := by
  unfold tailWord_3033020
  simp only [CollatzResearch.WordTrace]
  refine ⟨55311663735947006710568257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73748884981262675614091009 55311663735947006710568257)
  ·
    refine ⟨41483747801960255032926193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55311663735947006710568257 41483747801960255032926193)
    ·
      refine ⟨31112810851470191274694645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41483747801960255032926193 31112810851470191274694645)
      ·
        refine ⟨2916826017325330432002623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 31112810851470191274694645 2916826017325330432002623)
        ·
          refine ⟨4375239025987995648003935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2916826017325330432002623 4375239025987995648003935)
          ·
            refine ⟨6562858538981993472005903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4375239025987995648003935 6562858538981993472005903)
            ·
              refine ⟨9844287808472990208008855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6562858538981993472005903 9844287808472990208008855)
              ·
                refine ⟨14766431712709485312013283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9844287808472990208008855 14766431712709485312013283)
                ·
                  refine ⟨22149647569064227968019925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14766431712709485312013283 22149647569064227968019925)
                  ·
                    refine ⟨519132364899942843000467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 22149647569064227968019925 519132364899942843000467)
                    ·
                      rfl

theorem cell23_3033020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 1, 1, 1, 7].length) (baseStart_3033020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3033020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3033020 prefixEnd_3033020 := by exact prefixLift 3033020
  have htrace : WordTrace (prefixWord ++ tailWord_3033020) baseStart_3033020 baseEnd_3033020 := by
    simpa [prefixWord, tailWord_3033020, baseEnd_3033020] using wordTrace_append hprefix tailTrace_3033020
  have hstable : (prefixWord ++ tailWord_3033020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3033020).length < 2 ^ (prefixWord ++ tailWord_3033020).sum := by decide
  have hdescent : baseEnd_3033020 < baseStart_3033020 := by decide
  rcases family_descends (prefixWord ++ tailWord_3033020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3033023 : List Nat := [1, 1, 2, 2, 2, 1, 3, 2, 1, 6, 2]
def baseStart_3033023 : Nat := 118140960795 + 3033023 * 2 ^ 59
def prefixEnd_3033023 : Nat := 4983230072969 + 3 ^ 40 * 3033023 * 2
def baseEnd_3033023 : Nat := 1557398635141792017263887

theorem tailTrace_3033023 : CollatzResearch.WordTrace tailWord_3033023 prefixEnd_3033023 1557398635141792017263887 := by
  unfold tailWord_3033023
  simp only [CollatzResearch.WordTrace]
  refine ⟨110623436890883144933495723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73748957927255429955663815 110623436890883144933495723)
  ·
    refine ⟨165935155336324717400243585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110623436890883144933495723 165935155336324717400243585)
    ·
      refine ⟨124451366502243538050182689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 165935155336324717400243585 124451366502243538050182689)
      ·
        refine ⟨93338524876682653537637017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 124451366502243538050182689 93338524876682653537637017)
        ·
          refine ⟨70003893657511990153227763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93338524876682653537637017 70003893657511990153227763)
          ·
            refine ⟨105005840486267985229841645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70003893657511990153227763 105005840486267985229841645)
            ·
              refine ⟨39377190182350494461190617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 105005840486267985229841645 39377190182350494461190617)
              ·
                refine ⟨29532892636762870845892963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39377190182350494461190617 29532892636762870845892963)
                ·
                  refine ⟨44299338955144306268839445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29532892636762870845892963 44299338955144306268839445)
                  ·
                    refine ⟨2076531513522389356351849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 44299338955144306268839445 2076531513522389356351849)
                    ·
                      refine ⟨1557398635141792017263887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2076531513522389356351849 1557398635141792017263887)
                      ·
                        rfl

theorem cell23_3033023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 2, 1, 6, 2].length) (baseStart_3033023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3033023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3033023 prefixEnd_3033023 := by exact prefixLift 3033023
  have htrace : WordTrace (prefixWord ++ tailWord_3033023) baseStart_3033023 baseEnd_3033023 := by
    simpa [prefixWord, tailWord_3033023, baseEnd_3033023] using wordTrace_append hprefix tailTrace_3033023
  have hstable : (prefixWord ++ tailWord_3033023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3033023).length < 2 ^ (prefixWord ++ tailWord_3033023).sum := by decide
  have hdescent : baseEnd_3033023 < baseStart_3033023 := by decide
  rcases family_descends (prefixWord ++ tailWord_3033023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3033107 : List Nat := [1, 1, 1, 2, 1, 4, 2, 6, 1, 1, 3]
def baseStart_3033107 : Nat := 118140960795 + 3033107 * 2 ^ 59
def prefixEnd_3033107 : Nat := 4983230072969 + 3 ^ 40 * 3033107 * 2
def baseEnd_3033107 : Nat := 1557441767516769688613501

theorem tailTrace_3033107 : CollatzResearch.WordTrace tailWord_3033107 prefixEnd_3033107 1557441767516769688613501 := by
  unfold tailWord_3033107
  simp only [CollatzResearch.WordTrace]
  refine ⟨110626500622578827279553575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73751000415052551519702383 110626500622578827279553575)
  ·
    refine ⟨165939750933868240919330363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110626500622578827279553575 165939750933868240919330363)
    ·
      refine ⟨248909626400802361378995545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165939750933868240919330363 248909626400802361378995545)
      ·
        refine ⟨186682219800601771034246659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 248909626400802361378995545 186682219800601771034246659)
        ·
          refine ⟨280023329700902656551369989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 186682219800601771034246659 280023329700902656551369989)
          ·
            refine ⟨52504374318919248103381873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 280023329700902656551369989 52504374318919248103381873)
            ·
              refine ⟨39378280739189436077536405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52504374318919248103381873 39378280739189436077536405)
              ·
                refine ⟨1845856909649504816134519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 39378280739189436077536405 1845856909649504816134519)
                ·
                  refine ⟨2768785364474257224201779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1845856909649504816134519 2768785364474257224201779)
                  ·
                    refine ⟨4153178046711385836302669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2768785364474257224201779 4153178046711385836302669)
                    ·
                      refine ⟨1557441767516769688613501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4153178046711385836302669 1557441767516769688613501)
                      ·
                        rfl

theorem cell23_3033107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 6, 1, 1, 3].length) (baseStart_3033107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3033107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3033107 prefixEnd_3033107 := by exact prefixLift 3033107
  have htrace : WordTrace (prefixWord ++ tailWord_3033107) baseStart_3033107 baseEnd_3033107 := by
    simpa [prefixWord, tailWord_3033107, baseEnd_3033107] using wordTrace_append hprefix tailTrace_3033107
  have hstable : (prefixWord ++ tailWord_3033107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3033107).length < 2 ^ (prefixWord ++ tailWord_3033107).sum := by decide
  have hdescent : baseEnd_3033107 < baseStart_3033107 := by decide
  rcases family_descends (prefixWord ++ tailWord_3033107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3033113 : List Nat := [1, 2, 1, 2, 1, 1, 3, 4, 3, 1, 4]
def baseStart_3033113 : Nat := 118140960795 + 3033113 * 2 ^ 59
def prefixEnd_3033113 : Nat := 4983230072969 + 3 ^ 40 * 3033113 * 2
def baseEnd_3033113 : Nat := 1557444848400696665138473

theorem tailTrace_3033113 : CollatzResearch.WordTrace tailWord_3033113 prefixEnd_3033113 1557444848400696665138473 := by
  unfold tailWord_3033113
  simp only [CollatzResearch.WordTrace]
  refine ⟨110626719460557090304271993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73751146307038060202847995 110626719460557090304271993)
  ·
    refine ⟨82970039595417817728203995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110626719460557090304271993 82970039595417817728203995)
    ·
      refine ⟨124455059393126726592305993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82970039595417817728203995 124455059393126726592305993)
      ·
        refine ⟨93341294544845044944229495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 124455059393126726592305993 93341294544845044944229495)
        ·
          refine ⟨140011941817267567416344243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93341294544845044944229495 140011941817267567416344243)
          ·
            refine ⟨210017912725901351124516365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 140011941817267567416344243 210017912725901351124516365)
            ·
              refine ⟨78756717272213006671693637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 210017912725901351124516365 78756717272213006671693637)
              ·
                refine ⟨14766884488539938750942557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 78756717272213006671693637 14766884488539938750942557)
                ·
                  refine ⟨5537581683202477031603459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14766884488539938750942557 5537581683202477031603459)
                  ·
                    refine ⟨8306372524803715547405189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5537581683202477031603459 8306372524803715547405189)
                    ·
                      refine ⟨1557444848400696665138473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8306372524803715547405189 1557444848400696665138473)
                      ·
                        rfl

theorem cell23_3033113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 4, 3, 1, 4].length) (baseStart_3033113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3033113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3033113 prefixEnd_3033113 := by exact prefixLift 3033113
  have htrace : WordTrace (prefixWord ++ tailWord_3033113) baseStart_3033113 baseEnd_3033113 := by
    simpa [prefixWord, tailWord_3033113, baseEnd_3033113] using wordTrace_append hprefix tailTrace_3033113
  have hstable : (prefixWord ++ tailWord_3033113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3033113).length < 2 ^ (prefixWord ++ tailWord_3033113).sum := by decide
  have hdescent : baseEnd_3033113 < baseStart_3033113 := by decide
  rcases family_descends (prefixWord ++ tailWord_3033113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3033123 : List Nat := [1, 1, 1, 4, 3, 1, 2, 3, 1, 6]
def baseStart_3033123 : Nat := 118140960795 + 3033123 * 2 ^ 59
def prefixEnd_3033123 : Nat := 4983230072969 + 3 ^ 40 * 3033123 * 2
def baseEnd_3033123 : Nat := 519149994402413875337809

theorem tailTrace_3033123 : CollatzResearch.WordTrace tailWord_3033123 prefixEnd_3033123 519149994402413875337809 := by
  unfold tailWord_3033123
  simp only [CollatzResearch.WordTrace]
  refine ⟨110627084190520862012136023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73751389460347241341424015 110627084190520862012136023)
  ·
    refine ⟨165940626285781293018204035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110627084190520862012136023 165940626285781293018204035)
    ·
      refine ⟨248910939428671939527306053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165940626285781293018204035 248910939428671939527306053)
      ·
        refine ⟨46670801142875988661369885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 248910939428671939527306053 46670801142875988661369885)
        ·
          refine ⟨17501550428578495748013707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46670801142875988661369885 17501550428578495748013707)
          ·
            refine ⟨26252325642867743622020561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17501550428578495748013707 26252325642867743622020561)
            ·
              refine ⟨19689244232150807716515421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26252325642867743622020561 19689244232150807716515421)
              ·
                refine ⟨7383466587056552893693283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19689244232150807716515421 7383466587056552893693283)
                ·
                  refine ⟨11075199880584829340539925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7383466587056552893693283 11075199880584829340539925)
                  ·
                    refine ⟨519149994402413875337809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11075199880584829340539925 519149994402413875337809)
                    ·
                      rfl

theorem cell23_3033123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 2, 3, 1, 6].length) (baseStart_3033123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3033123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3033123 prefixEnd_3033123 := by exact prefixLift 3033123
  have htrace : WordTrace (prefixWord ++ tailWord_3033123) baseStart_3033123 baseEnd_3033123 := by
    simpa [prefixWord, tailWord_3033123, baseEnd_3033123] using wordTrace_append hprefix tailTrace_3033123
  have hstable : (prefixWord ++ tailWord_3033123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3033123).length < 2 ^ (prefixWord ++ tailWord_3033123).sum := by decide
  have hdescent : baseEnd_3033123 < baseStart_3033123 := by decide
  rcases family_descends (prefixWord ++ tailWord_3033123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3033127 : List Nat := [1, 1, 7, 1, 2, 1, 1, 1, 3, 5]
def baseStart_3033127 : Nat := 118140960795 + 3033127 * 2 ^ 59
def prefixEnd_3033127 : Nat := 4983230072969 + 3 ^ 40 * 3033127 * 2
def baseEnd_3033127 : Nat := 519150679043286536787803

theorem tailTrace_3033127 : CollatzResearch.WordTrace tailWord_3033127 prefixEnd_3033127 519150679043286536787803 := by
  unfold tailWord_3033127
  simp only [CollatzResearch.WordTrace]
  refine ⟨110627230082506370695281635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73751486721670913796854423 110627230082506370695281635)
  ·
    refine ⟨165940845123759556042922453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110627230082506370695281635 165940845123759556042922453)
    ·
      refine ⟨3889238557588114594755995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 165940845123759556042922453 3889238557588114594755995)
      ·
        refine ⟨5833857836382171892133993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3889238557588114594755995 5833857836382171892133993)
        ·
          refine ⟨4375393377286628919100495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5833857836382171892133993 4375393377286628919100495)
          ·
            refine ⟨6563090065929943378650743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4375393377286628919100495 6563090065929943378650743)
            ·
              refine ⟨9844635098894915067976115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6563090065929943378650743 9844635098894915067976115)
              ·
                refine ⟨14766952648342372601964173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9844635098894915067976115 14766952648342372601964173)
                ·
                  refine ⟨5537607243128389725736565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14766952648342372601964173 5537607243128389725736565)
                  ·
                    refine ⟨519150679043286536787803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5537607243128389725736565 519150679043286536787803)
                    ·
                      rfl

theorem cell23_3033127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 1, 1, 3, 5].length) (baseStart_3033127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3033127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3033127 prefixEnd_3033127 := by exact prefixLift 3033127
  have htrace : WordTrace (prefixWord ++ tailWord_3033127) baseStart_3033127 baseEnd_3033127 := by
    simpa [prefixWord, tailWord_3033127, baseEnd_3033127] using wordTrace_append hprefix tailTrace_3033127
  have hstable : (prefixWord ++ tailWord_3033127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3033127).length < 2 ^ (prefixWord ++ tailWord_3033127).sum := by decide
  have hdescent : baseEnd_3033127 < baseStart_3033127 := by decide
  rcases family_descends (prefixWord ++ tailWord_3033127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3033134 : List Nat := [4, 1, 3, 1, 1, 3, 2, 1, 2, 3, 2]
def baseStart_3033134 : Nat := 118140960795 + 3033134 * 2 ^ 59
def prefixEnd_3033134 : Nat := 4983230072969 + 3 ^ 40 * 3033134 * 2
def baseEnd_3033134 : Nat := 1557455631494441082975877

theorem tailTrace_3033134 : CollatzResearch.WordTrace tailWord_3033134 prefixEnd_3033134 1557455631494441082975877 := by
  unfold tailWord_3033134
  simp only [CollatzResearch.WordTrace]
  refine ⟨13828435674185126361348307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 73751656928987340593857637 13828435674185126361348307)
  ·
    refine ⟨20742653511277689542022461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13828435674185126361348307 20742653511277689542022461)
    ·
      refine ⟨7778495066729133578258423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20742653511277689542022461 7778495066729133578258423)
      ·
        refine ⟨11667742600093700367387635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7778495066729133578258423 11667742600093700367387635)
        ·
          refine ⟨17501613900140550551081453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11667742600093700367387635 17501613900140550551081453)
          ·
            refine ⟨6563105212552706456655545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17501613900140550551081453 6563105212552706456655545)
            ·
              refine ⟨4922328909414529842491659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6563105212552706456655545 4922328909414529842491659)
              ·
                refine ⟨7383493364121794763737489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4922328909414529842491659 7383493364121794763737489)
                ·
                  refine ⟨5537620023091346072803117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7383493364121794763737489 5537620023091346072803117)
                  ·
                    refine ⟨2076607508659254777301169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5537620023091346072803117 2076607508659254777301169)
                    ·
                      refine ⟨1557455631494441082975877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2076607508659254777301169 1557455631494441082975877)
                      ·
                        rfl

theorem cell23_3033134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 2, 1, 2, 3, 2].length) (baseStart_3033134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3033134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3033134 prefixEnd_3033134 := by exact prefixLift 3033134
  have htrace : WordTrace (prefixWord ++ tailWord_3033134) baseStart_3033134 baseEnd_3033134 := by
    simpa [prefixWord, tailWord_3033134, baseEnd_3033134] using wordTrace_append hprefix tailTrace_3033134
  have hstable : (prefixWord ++ tailWord_3033134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3033134).length < 2 ^ (prefixWord ++ tailWord_3033134).sum := by decide
  have hdescent : baseEnd_3033134 < baseStart_3033134 := by decide
  rcases family_descends (prefixWord ++ tailWord_3033134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3033143 : List Nat := [1, 1, 3, 1, 2, 2, 3, 1, 3, 2, 4]
def baseStart_3033143 : Nat := 118140960795 + 3033143 * 2 ^ 59
def prefixEnd_3033143 : Nat := 4983230072969 + 3 ^ 40 * 3033143 * 2
def baseEnd_3033143 : Nat := 1557460252820331547763335

theorem tailTrace_3033143 : CollatzResearch.WordTrace tailWord_3033143 prefixEnd_3033143 1557460252820331547763335 := by
  unfold tailWord_3033143
  simp only [CollatzResearch.WordTrace]
  refine ⟨110627813650448405427864083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73751875766965603618576055 110627813650448405427864083)
  ·
    refine ⟨165941720475672608141796125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110627813650448405427864083 165941720475672608141796125)
    ·
      refine ⟨62228145178377228053173547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 165941720475672608141796125 62228145178377228053173547)
      ·
        refine ⟨93342217767565842079760321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62228145178377228053173547 93342217767565842079760321)
        ·
          refine ⟨70006663325674381559820241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93342217767565842079760321 70006663325674381559820241)
          ·
            refine ⟨52504997494255786169865181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70006663325674381559820241 52504997494255786169865181)
            ·
              refine ⟨19689374060345919813699443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52504997494255786169865181 19689374060345919813699443)
              ·
                refine ⟨29534061090518879720549165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19689374060345919813699443 29534061090518879720549165)
                ·
                  refine ⟨11075272908944579895205937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29534061090518879720549165 11075272908944579895205937)
                  ·
                    refine ⟨8306454681708434921404453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11075272908944579895205937 8306454681708434921404453)
                    ·
                      refine ⟨1557460252820331547763335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8306454681708434921404453 1557460252820331547763335)
                      ·
                        rfl

theorem cell23_3033143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 3, 1, 3, 2, 4].length) (baseStart_3033143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3033143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3033143 prefixEnd_3033143 := by exact prefixLift 3033143
  have htrace : WordTrace (prefixWord ++ tailWord_3033143) baseStart_3033143 baseEnd_3033143 := by
    simpa [prefixWord, tailWord_3033143, baseEnd_3033143] using wordTrace_append hprefix tailTrace_3033143
  have hstable : (prefixWord ++ tailWord_3033143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3033143).length < 2 ^ (prefixWord ++ tailWord_3033143).sum := by decide
  have hdescent : baseEnd_3033143 < baseStart_3033143 := by decide
  rcases family_descends (prefixWord ++ tailWord_3033143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3033153 : List Nat := [1, 2, 5, 1, 2, 12]
def baseStart_3033153 : Nat := 118140960795 + 3033153 * 2 ^ 59
def prefixEnd_3033153 : Nat := 4983230072969 + 3 ^ 40 * 3033153 * 2
def baseEnd_3033153 : Nat := 6409322582826652298923

theorem tailTrace_3033153 : CollatzResearch.WordTrace tailWord_3033153 prefixEnd_3033153 6409322582826652298923 := by
  unfold tailWord_3033153
  simp only [CollatzResearch.WordTrace]
  refine ⟨110628178380412177135728113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73752118920274784757152075 110628178380412177135728113)
  ·
    refine ⟨82971133785309132851796085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110628178380412177135728113 82971133785309132851796085)
    ·
      refine ⟨7778543792372731204855883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 82971133785309132851796085 7778543792372731204855883)
      ·
        refine ⟨11667815688559096807283825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7778543792372731204855883 11667815688559096807283825)
        ·
          refine ⟨8750861766419322605462869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11667815688559096807283825 8750861766419322605462869)
          ·
            refine ⟨6409322582826652298923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 8750861766419322605462869 6409322582826652298923)
            ·
              rfl

theorem cell23_3033153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 12].length) (baseStart_3033153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3033153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3033153 prefixEnd_3033153 := by exact prefixLift 3033153
  have htrace : WordTrace (prefixWord ++ tailWord_3033153) baseStart_3033153 baseEnd_3033153 := by
    simpa [prefixWord, tailWord_3033153, baseEnd_3033153] using wordTrace_append hprefix tailTrace_3033153
  have hstable : (prefixWord ++ tailWord_3033153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3033153).length < 2 ^ (prefixWord ++ tailWord_3033153).sum := by decide
  have hdescent : baseEnd_3033153 < baseStart_3033153 := by decide
  rcases family_descends (prefixWord ++ tailWord_3033153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3033174 : List Nat := [5, 2, 2, 1, 1, 2, 2, 1, 1, 6]
def baseStart_3033174 : Nat := 118140960795 + 3033174 * 2 ^ 59
def prefixEnd_3033174 : Nat := 4983230072969 + 3 ^ 40 * 3033174 * 2
def baseEnd_3033174 : Nat := 519158723573540308825231

theorem tailTrace_3033174 : CollatzResearch.WordTrace tailWord_3033174 prefixEnd_3033174 519158723573540308825231 := by
  unfold tailWord_3033174
  simp only [CollatzResearch.WordTrace]
  refine ⟨6914309019583506107640161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 73752629542224065148161717 6914309019583506107640161)
  ·
    refine ⟨5185731764687629580730121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6914309019583506107640161 5185731764687629580730121)
    ·
      refine ⟨3889298823515722185547591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5185731764687629580730121 3889298823515722185547591)
      ·
        refine ⟨5833948235273583278321387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3889298823515722185547591 5833948235273583278321387)
        ·
          refine ⟨8750922352910374917482081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5833948235273583278321387 8750922352910374917482081)
          ·
            refine ⟨6563191764682781188111561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8750922352910374917482081 6563191764682781188111561)
            ·
              refine ⟨4922393823512085891083671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6563191764682781188111561 4922393823512085891083671)
              ·
                refine ⟨7383590735268128836625507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4922393823512085891083671 7383590735268128836625507)
                ·
                  refine ⟨11075386102902193254938261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7383590735268128836625507 11075386102902193254938261)
                  ·
                    refine ⟨519158723573540308825231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11075386102902193254938261 519158723573540308825231)
                    ·
                      rfl

theorem cell23_3033174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 2, 1, 1, 6].length) (baseStart_3033174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3033174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3033174 prefixEnd_3033174 := by exact prefixLift 3033174
  have htrace : WordTrace (prefixWord ++ tailWord_3033174) baseStart_3033174 baseEnd_3033174 := by
    simpa [prefixWord, tailWord_3033174, baseEnd_3033174] using wordTrace_append hprefix tailTrace_3033174
  have hstable : (prefixWord ++ tailWord_3033174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3033174).length < 2 ^ (prefixWord ++ tailWord_3033174).sum := by decide
  have hdescent : baseEnd_3033174 < baseStart_3033174 := by decide
  rcases family_descends (prefixWord ++ tailWord_3033174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3033181 : List Nat := [1, 4, 4, 1, 1, 2, 1, 2, 3, 2, 2]
def baseStart_3033181 : Nat := 118140960795 + 3033181 * 2 ^ 59
def prefixEnd_3033181 : Nat := 4983230072969 + 3 ^ 40 * 3033181 * 2
def baseEnd_3033181 : Nat := 1557479765085202399088161

theorem tailTrace_3033181 : CollatzResearch.WordTrace tailWord_3033181 prefixEnd_3033181 1557479765085202399088161 := by
  unfold tailWord_3033181
  simp only [CollatzResearch.WordTrace]
  refine ⟨110629199624310737917747397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73752799749540491945164931 110629199624310737917747397)
  ·
    refine ⟨20742974929558263359577637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 110629199624310737917747397 20742974929558263359577637)
    ·
      refine ⟨3889307799292174379920807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20742974929558263359577637 3889307799292174379920807)
      ·
        refine ⟨5833961698938261569881211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3889307799292174379920807 5833961698938261569881211)
        ·
          refine ⟨8750942548407392354821817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5833961698938261569881211 8750942548407392354821817)
          ·
            refine ⟨6563206911305544266116363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8750942548407392354821817 6563206911305544266116363)
            ·
              refine ⟨9844810366958316399174545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6563206911305544266116363 9844810366958316399174545)
              ·
                refine ⟨7383607775218737299380909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9844810366958316399174545 7383607775218737299380909)
                ·
                  refine ⟨2768852915707026487267841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7383607775218737299380909 2768852915707026487267841)
                  ·
                    refine ⟨2076639686780269865450881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2768852915707026487267841 2076639686780269865450881)
                    ·
                      refine ⟨1557479765085202399088161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2076639686780269865450881 1557479765085202399088161)
                      ·
                        rfl

theorem cell23_3033181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 1, 2, 3, 2, 2].length) (baseStart_3033181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3033181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3033181 prefixEnd_3033181 := by exact prefixLift 3033181
  have htrace : WordTrace (prefixWord ++ tailWord_3033181) baseStart_3033181 baseEnd_3033181 := by
    simpa [prefixWord, tailWord_3033181, baseEnd_3033181] using wordTrace_append hprefix tailTrace_3033181
  have hstable : (prefixWord ++ tailWord_3033181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3033181).length < 2 ^ (prefixWord ++ tailWord_3033181).sum := by decide
  have hdescent : baseEnd_3033181 < baseStart_3033181 := by decide
  rcases family_descends (prefixWord ++ tailWord_3033181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3033193 : List Nat := [1, 2, 1, 1, 1, 5, 2, 1, 2, 2, 5]
def baseStart_3033193 : Nat := 118140960795 + 3033193 * 2 ^ 59
def prefixEnd_3033193 : Nat := 4983230072969 + 3 ^ 40 * 3033193 * 2
def baseEnd_3033193 : Nat := 1557485926853056352138105

theorem tailTrace_3033193 : CollatzResearch.WordTrace tailWord_3033193 prefixEnd_3033193 1557485926853056352138105 := by
  unfold tailWord_3033193
  simp only [CollatzResearch.WordTrace]
  refine ⟨110629637300267263967184233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73753091533511509311456155 110629637300267263967184233)
  ·
    refine ⟨82972227975200447975388175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110629637300267263967184233 82972227975200447975388175)
    ·
      refine ⟨124458341962800671963082263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82972227975200447975388175 124458341962800671963082263)
      ·
        refine ⟨186687512944201007944623395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124458341962800671963082263 186687512944201007944623395)
        ·
          refine ⟨280031269416301511916935093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 186687512944201007944623395 280031269416301511916935093)
          ·
            refine ⟨26252931507778266742212665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 280031269416301511916935093 26252931507778266742212665)
            ·
              refine ⟨19689698630833700056659499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26252931507778266742212665 19689698630833700056659499)
              ·
                refine ⟨29534547946250550084989249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19689698630833700056659499 29534547946250550084989249)
                ·
                  refine ⟨22150910959687912563741937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29534547946250550084989249 22150910959687912563741937)
                  ·
                    refine ⟨16613183219765934422806453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22150910959687912563741937 16613183219765934422806453)
                    ·
                      refine ⟨1557485926853056352138105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16613183219765934422806453 1557485926853056352138105)
                      ·
                        rfl

theorem cell23_3033193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 2, 1, 2, 2, 5].length) (baseStart_3033193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3033193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3033193 prefixEnd_3033193 := by exact prefixLift 3033193
  have htrace : WordTrace (prefixWord ++ tailWord_3033193) baseStart_3033193 baseEnd_3033193 := by
    simpa [prefixWord, tailWord_3033193, baseEnd_3033193] using wordTrace_append hprefix tailTrace_3033193
  have hstable : (prefixWord ++ tailWord_3033193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3033193).length < 2 ^ (prefixWord ++ tailWord_3033193).sum := by decide
  have hdescent : baseEnd_3033193 < baseStart_3033193 := by decide
  rcases family_descends (prefixWord ++ tailWord_3033193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3033197 : List Nat := [1, 5, 1, 1, 2, 1, 2, 2, 4, 1, 3]
def baseStart_3033197 : Nat := 118140960795 + 3033197 * 2 ^ 59
def prefixEnd_3033197 : Nat := 4983230072969 + 3 ^ 40 * 3033197 * 2
def baseEnd_3033197 : Nat := 1557487980775674336488087

theorem tailTrace_3033197 : CollatzResearch.WordTrace tailWord_3033197 prefixEnd_3033197 1557487980775674336488087 := by
  unfold tailWord_3033197
  simp only [CollatzResearch.WordTrace]
  refine ⟨110629783192252772650329845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73753188794835181766886563 110629783192252772650329845)
  ·
    refine ⟨10371542174273697435968423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 110629783192252772650329845 10371542174273697435968423)
    ·
      refine ⟨15557313261410546153952635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10371542174273697435968423 15557313261410546153952635)
      ·
        refine ⟨23335969892115819230928953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15557313261410546153952635 23335969892115819230928953)
        ·
          refine ⟨17501977419086864423196715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23335969892115819230928953 17501977419086864423196715)
          ·
            refine ⟨26252966128630296634795073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17501977419086864423196715 26252966128630296634795073)
            ·
              refine ⟨19689724596472722476096305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26252966128630296634795073 19689724596472722476096305)
              ·
                refine ⟨14767293447354541857072229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19689724596472722476096305 14767293447354541857072229)
                ·
                  refine ⟨2768867521378976598201043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14767293447354541857072229 2768867521378976598201043)
                  ·
                    refine ⟨4153301282068464897301565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2768867521378976598201043 4153301282068464897301565)
                    ·
                      refine ⟨1557487980775674336488087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4153301282068464897301565 1557487980775674336488087)
                      ·
                        rfl

theorem cell23_3033197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 2, 2, 4, 1, 3].length) (baseStart_3033197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3033197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3033197 prefixEnd_3033197 := by exact prefixLift 3033197
  have htrace : WordTrace (prefixWord ++ tailWord_3033197) baseStart_3033197 baseEnd_3033197 := by
    simpa [prefixWord, tailWord_3033197, baseEnd_3033197] using wordTrace_append hprefix tailTrace_3033197
  have hstable : (prefixWord ++ tailWord_3033197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3033197).length < 2 ^ (prefixWord ++ tailWord_3033197).sum := by decide
  have hdescent : baseEnd_3033197 < baseStart_3033197 := by decide
  rcases family_descends (prefixWord ++ tailWord_3033197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3033243 : List Nat := [1, 1, 1, 1, 1, 1, 2, 8, 7]
def baseStart_3033243 : Nat := 118140960795 + 3033243 * 2 ^ 59
def prefixEnd_3033243 : Nat := 4983230072969 + 3 ^ 40 * 3033243 * 2
def baseEnd_3033243 : Nat := 173056844542864572945875

theorem tailTrace_3033243 : CollatzResearch.WordTrace tailWord_3033243 prefixEnd_3033243 173056844542864572945875 := by
  unfold tailWord_3033243
  simp only [CollatzResearch.WordTrace]
  refine ⟨110631460950086122506504383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73754307300057415004336255 110631460950086122506504383)
  ·
    refine ⟨165947191425129183759756575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110631460950086122506504383 165947191425129183759756575)
    ·
      refine ⟨248920787137693775639634863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165947191425129183759756575 248920787137693775639634863)
      ·
        refine ⟨373381180706540663459452295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 248920787137693775639634863 373381180706540663459452295)
        ·
          refine ⟨560071771059810995189178443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 373381180706540663459452295 560071771059810995189178443)
          ·
            refine ⟨840107656589716492783767665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 560071771059810995189178443 840107656589716492783767665)
            ·
              refine ⟨630080742442287369587825749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 840107656589716492783767665 630080742442287369587825749)
              ·
                refine ⟨7383758700495555112357333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 630080742442287369587825749 7383758700495555112357333)
                ·
                  refine ⟨173056844542864572945875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7383758700495555112357333 173056844542864572945875)
                  ·
                    rfl

theorem cell23_3033243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 8, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 8, 7].length) (baseStart_3033243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3033243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3033243 prefixEnd_3033243 := by exact prefixLift 3033243
  have htrace : WordTrace (prefixWord ++ tailWord_3033243) baseStart_3033243 baseEnd_3033243 := by
    simpa [prefixWord, tailWord_3033243, baseEnd_3033243] using wordTrace_append hprefix tailTrace_3033243
  have hstable : (prefixWord ++ tailWord_3033243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3033243).length < 2 ^ (prefixWord ++ tailWord_3033243).sum := by decide
  have hdescent : baseEnd_3033243 < baseStart_3033243 := by decide
  rcases family_descends (prefixWord ++ tailWord_3033243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3033290 : List Nat := [3, 1, 2, 1, 3, 1, 1, 2, 4, 5]
def baseStart_3033290 : Nat := 118140960795 + 3033290 * 2 ^ 59
def prefixEnd_3033290 : Nat := 4983230072969 + 3 ^ 40 * 3033290 * 2
def baseEnd_3033290 : Nat := 519178578158847490875053

theorem tailTrace_3033290 : CollatzResearch.WordTrace tailWord_3033290 prefixEnd_3033290 519178578158847490875053 := by
  unfold tailWord_3033290
  simp only [CollatzResearch.WordTrace]
  refine ⟨27658293795228962383366331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73755450120610566355643549 27658293795228962383366331)
  ·
    refine ⟨41487440692843443575049497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27658293795228962383366331 41487440692843443575049497)
    ·
      refine ⟨31115580519632582681287123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41487440692843443575049497 31115580519632582681287123)
      ·
        refine ⟨46673370779448874021930685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31115580519632582681287123 46673370779448874021930685)
        ·
          refine ⟨17502514042293327758224007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46673370779448874021930685 17502514042293327758224007)
          ·
            refine ⟨26253771063439991637336011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17502514042293327758224007 26253771063439991637336011)
            ·
              refine ⟨39380656595159987456004017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26253771063439991637336011 39380656595159987456004017)
              ·
                refine ⟨29535492446369990592003013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39380656595159987456004017 29535492446369990592003013)
                ·
                  refine ⟨5537904833694373236000565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29535492446369990592003013 5537904833694373236000565)
                  ·
                    refine ⟨519178578158847490875053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5537904833694373236000565 519178578158847490875053)
                    ·
                      rfl

theorem cell23_3033290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 2, 4, 5].length) (baseStart_3033290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3033290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3033290 prefixEnd_3033290 := by exact prefixLift 3033290
  have htrace : WordTrace (prefixWord ++ tailWord_3033290) baseStart_3033290 baseEnd_3033290 := by
    simpa [prefixWord, tailWord_3033290, baseEnd_3033290] using wordTrace_append hprefix tailTrace_3033290
  have hstable : (prefixWord ++ tailWord_3033290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3033290).length < 2 ^ (prefixWord ++ tailWord_3033290).sum := by decide
  have hdescent : baseEnd_3033290 < baseStart_3033290 := by decide
  rcases family_descends (prefixWord ++ tailWord_3033290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3033327 : List Nat := [1, 1, 2, 1, 6, 1, 2, 2, 2, 1, 4]
def baseStart_3033327 : Nat := 118140960795 + 3033327 * 2 ^ 59
def prefixEnd_3033327 : Nat := 4983230072969 + 3 ^ 40 * 3033327 * 2
def baseEnd_3033327 : Nat := 1557554733260758827862489

theorem tailTrace_3033327 : CollatzResearch.WordTrace tailWord_3033327 prefixEnd_3033327 1557554733260758827862489 := by
  unfold tailWord_3033327
  simp only [CollatzResearch.WordTrace]
  refine ⟨110634524681781804852562235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73756349787854536568374823 110634524681781804852562235)
  ·
    refine ⟨165951787022672707278843353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110634524681781804852562235 165951787022672707278843353)
    ·
      refine ⟨124463840267004530459132515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 165951787022672707278843353 124463840267004530459132515)
      ·
        refine ⟨186695760400506795688698773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124463840267004530459132515 186695760400506795688698773)
        ·
          refine ⟨8751363768773756047907755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 186695760400506795688698773 8751363768773756047907755)
          ·
            refine ⟨13127045653160634071861633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8751363768773756047907755 13127045653160634071861633)
            ·
              refine ⟨9845284239870475553896225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13127045653160634071861633 9845284239870475553896225)
              ·
                refine ⟨7383963179902856665422169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9845284239870475553896225 7383963179902856665422169)
                ·
                  refine ⟨5537972384927142499066627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7383963179902856665422169 5537972384927142499066627)
                  ·
                    refine ⟨8306958577390713748599941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5537972384927142499066627 8306958577390713748599941)
                    ·
                      refine ⟨1557554733260758827862489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8306958577390713748599941 1557554733260758827862489)
                      ·
                        rfl

theorem cell23_3033327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 2, 2, 2, 1, 4].length) (baseStart_3033327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3033327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3033327 prefixEnd_3033327 := by exact prefixLift 3033327
  have htrace : WordTrace (prefixWord ++ tailWord_3033327) baseStart_3033327 baseEnd_3033327 := by
    simpa [prefixWord, tailWord_3033327, baseEnd_3033327] using wordTrace_append hprefix tailTrace_3033327
  have hstable : (prefixWord ++ tailWord_3033327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3033327).length < 2 ^ (prefixWord ++ tailWord_3033327).sum := by decide
  have hdescent : baseEnd_3033327 < baseStart_3033327 := by decide
  rcases family_descends (prefixWord ++ tailWord_3033327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3033374 : List Nat := [4, 3, 2, 1, 1, 1, 1, 1, 2, 1, 6]
def baseStart_3033374 : Nat := 118140960795 + 3033374 * 2 ^ 59
def prefixEnd_3033374 : Nat := 4983230072969 + 3 ^ 40 * 3033374 * 2
def baseEnd_3033374 : Nat := 1557578866851520143974773

theorem tailTrace_3033374 : CollatzResearch.WordTrace tailWord_3033374 prefixEnd_3033374 1557578866851520143974773 := by
  unfold tailWord_3033374
  simp only [CollatzResearch.WordTrace]
  refine ⟨13829529864076441484940397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 73757492608407687919682117 13829529864076441484940397)
  ·
    refine ⟨5186073699028665556852649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13829529864076441484940397 5186073699028665556852649)
    ·
      refine ⟨3889555274271499167639487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5186073699028665556852649 3889555274271499167639487)
      ·
        refine ⟨5834332911407248751459231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3889555274271499167639487 5834332911407248751459231)
        ·
          refine ⟨8751499367110873127188847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5834332911407248751459231 8751499367110873127188847)
          ·
            refine ⟨13127249050666309690783271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8751499367110873127188847 13127249050666309690783271)
            ·
              refine ⟨19690873575999464536174907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13127249050666309690783271 19690873575999464536174907)
              ·
                refine ⟨29536310363999196804262361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19690873575999464536174907 29536310363999196804262361)
                ·
                  refine ⟨22152232772999397603196771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29536310363999196804262361 22152232772999397603196771)
                  ·
                    refine ⟨33228349159499096404795157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22152232772999397603196771 33228349159499096404795157)
                    ·
                      refine ⟨1557578866851520143974773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 33228349159499096404795157 1557578866851520143974773)
                      ·
                        rfl

theorem cell23_3033374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 1, 1, 2, 1, 6].length) (baseStart_3033374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3033374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3033374 prefixEnd_3033374 := by exact prefixLift 3033374
  have htrace : WordTrace (prefixWord ++ tailWord_3033374) baseStart_3033374 baseEnd_3033374 := by
    simpa [prefixWord, tailWord_3033374, baseEnd_3033374] using wordTrace_append hprefix tailTrace_3033374
  have hstable : (prefixWord ++ tailWord_3033374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3033374).length < 2 ^ (prefixWord ++ tailWord_3033374).sum := by decide
  have hdescent : baseEnd_3033374 < baseStart_3033374 := by decide
  rcases family_descends (prefixWord ++ tailWord_3033374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3033417 : List Nat := [1, 2, 1, 1, 2, 3, 1, 1, 1, 8, 2]
def baseStart_3033417 : Nat := 118140960795 + 3033417 * 2 ^ 59
def prefixEnd_3033417 : Nat := 4983230072969 + 3 ^ 40 * 3033417 * 2
def baseEnd_3033417 : Nat := 1557600946519663475737075

theorem tailTrace_3033417 : CollatzResearch.WordTrace tailWord_3033417 prefixEnd_3033417 1557600946519663475737075 := by
  unfold tailWord_3033417
  simp only [CollatzResearch.WordTrace]
  refine ⟨110637807251455750223338505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73758538167637166815559003 110637807251455750223338505)
  ·
    refine ⟨82978355438591812667503879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110637807251455750223338505 82978355438591812667503879)
    ·
      refine ⟨124467533157887719001255819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82978355438591812667503879 124467533157887719001255819)
      ·
        refine ⟨186701299736831578501883729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124467533157887719001255819 186701299736831578501883729)
        ·
          refine ⟨140025974802623683876412797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 186701299736831578501883729 140025974802623683876412797)
          ·
            refine ⟨52509740550983881453654799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 140025974802623683876412797 52509740550983881453654799)
            ·
              refine ⟨78764610826475822180482199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52509740550983881453654799 78764610826475822180482199)
              ·
                refine ⟨118146916239713733270723299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 78764610826475822180482199 118146916239713733270723299)
                ·
                  refine ⟨177220374359570599906084949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 118146916239713733270723299 177220374359570599906084949)
                  ·
                    refine ⟨2076801262026217967649433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 177220374359570599906084949 2076801262026217967649433)
                    ·
                      refine ⟨1557600946519663475737075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2076801262026217967649433 1557600946519663475737075)
                      ·
                        rfl

theorem cell23_3033417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 1, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 1, 1, 8, 2].length) (baseStart_3033417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3033417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3033417 prefixEnd_3033417 := by exact prefixLift 3033417
  have htrace : WordTrace (prefixWord ++ tailWord_3033417) baseStart_3033417 baseEnd_3033417 := by
    simpa [prefixWord, tailWord_3033417, baseEnd_3033417] using wordTrace_append hprefix tailTrace_3033417
  have hstable : (prefixWord ++ tailWord_3033417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3033417).length < 2 ^ (prefixWord ++ tailWord_3033417).sum := by decide
  have hdescent : baseEnd_3033417 < baseStart_3033417 := by decide
  rcases family_descends (prefixWord ++ tailWord_3033417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3033428 : List Nat := [2, 4, 1, 1, 2, 2, 3, 3, 1, 1, 3]
def baseStart_3033428 : Nat := 118140960795 + 3033428 * 2 ^ 59
def prefixEnd_3033428 : Nat := 4983230072969 + 3 ^ 40 * 3033428 * 2
def baseEnd_3033428 : Nat := 1557606594806862932699525

theorem tailTrace_3033428 : CollatzResearch.WordTrace tailWord_3033428 prefixEnd_3033428 1557606594806862932699525 := by
  unfold tailWord_3033428
  simp only [CollatzResearch.WordTrace]
  refine ⟨55319104227207949550994469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73758805636277266067992625 55319104227207949550994469)
  ·
    refine ⟨10372332042601490540811463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 55319104227207949550994469 10372332042601490540811463)
    ·
      refine ⟨15558498063902235811217195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10372332042601490540811463 15558498063902235811217195)
      ·
        refine ⟨23337747095853353716825793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15558498063902235811217195 23337747095853353716825793)
        ·
          refine ⟨17503310321890015287619345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23337747095853353716825793 17503310321890015287619345)
          ·
            refine ⟨13127482741417511465714509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17503310321890015287619345 13127482741417511465714509)
            ·
              refine ⟨4922806028031566799642941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13127482741417511465714509 4922806028031566799642941)
              ·
                refine ⟨1846052260511837549866103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4922806028031566799642941 1846052260511837549866103)
                ·
                  refine ⟨2769078390767756324799155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1846052260511837549866103 2769078390767756324799155)
                  ·
                    refine ⟨4153617586151634487198733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2769078390767756324799155 4153617586151634487198733)
                    ·
                      refine ⟨1557606594806862932699525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4153617586151634487198733 1557606594806862932699525)
                      ·
                        rfl

theorem cell23_3033428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 3, 3, 1, 1, 3].length) (baseStart_3033428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3033428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3033428 prefixEnd_3033428 := by exact prefixLift 3033428
  have htrace : WordTrace (prefixWord ++ tailWord_3033428) baseStart_3033428 baseEnd_3033428 := by
    simpa [prefixWord, tailWord_3033428, baseEnd_3033428] using wordTrace_append hprefix tailTrace_3033428
  have hstable : (prefixWord ++ tailWord_3033428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3033428).length < 2 ^ (prefixWord ++ tailWord_3033428).sum := by decide
  have hdescent : baseEnd_3033428 < baseStart_3033428 := by decide
  rcases family_descends (prefixWord ++ tailWord_3033428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3033444 : List Nat := [2, 3, 1, 1, 3, 1, 2, 4, 2, 4]
def baseStart_3033444 : Nat := 118140960795 + 3033444 * 2 ^ 59
def prefixEnd_3033444 : Nat := 4983230072969 + 3 ^ 40 * 3033444 * 2
def baseEnd_3033444 : Nat := 519204936832444956699817

theorem tailTrace_3033444 : CollatzResearch.WordTrace tailWord_3033444 prefixEnd_3033444 519204936832444956699817 := by
  unfold tailWord_3033444
  simp only [CollatzResearch.WordTrace]
  refine ⟨55319396011178966917285693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73759194681571955889714257 55319396011178966917285693)
  ·
    refine ⟨20744773504192112593982135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55319396011178966917285693 20744773504192112593982135)
    ·
      refine ⟨31117160256288168890973203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20744773504192112593982135 31117160256288168890973203)
      ·
        refine ⟨46675740384432253336459805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31117160256288168890973203 46675740384432253336459805)
        ·
          refine ⟨17503402644162095001172427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46675740384432253336459805 17503402644162095001172427)
          ·
            refine ⟨26255103966243142501758641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17503402644162095001172427 26255103966243142501758641)
            ·
              refine ⟨19691327974682356876318981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26255103966243142501758641 19691327974682356876318981)
              ·
                refine ⟨3692123995252941914309809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19691327974682356876318981 3692123995252941914309809)
                ·
                  refine ⟨2769092996439706435732357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3692123995252941914309809 2769092996439706435732357)
                  ·
                    refine ⟨519204936832444956699817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2769092996439706435732357 519204936832444956699817)
                    ·
                      rfl

theorem cell23_3033444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 2, 4, 2, 4].length) (baseStart_3033444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3033444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3033444 prefixEnd_3033444 := by exact prefixLift 3033444
  have htrace : WordTrace (prefixWord ++ tailWord_3033444) baseStart_3033444 baseEnd_3033444 := by
    simpa [prefixWord, tailWord_3033444, baseEnd_3033444] using wordTrace_append hprefix tailTrace_3033444
  have hstable : (prefixWord ++ tailWord_3033444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3033444).length < 2 ^ (prefixWord ++ tailWord_3033444).sum := by decide
  have hdescent : baseEnd_3033444 < baseStart_3033444 := by decide
  rcases family_descends (prefixWord ++ tailWord_3033444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3033447 : List Nat := [1, 1, 5, 1, 3, 1, 1, 2, 1, 1, 6]
def baseStart_3033447 : Nat := 118140960795 + 3033447 * 2 ^ 59
def prefixEnd_3033447 : Nat := 4983230072969 + 3 ^ 40 * 3033447 * 2
def baseEnd_3033447 : Nat := 1557616350939298358361937

theorem tailTrace_3033447 : CollatzResearch.WordTrace tailWord_3033447 prefixEnd_3033447 1557616350939298358361937 := by
  unfold tailWord_3033447
  simp only [CollatzResearch.WordTrace]
  refine ⟨110638901441347065346930595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73759267627564710231287063 110638901441347065346930595)
  ·
    refine ⟨165958352162020598020395893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110638901441347065346930595 165958352162020598020395893)
    ·
      refine ⟨15558595515189431064412115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 165958352162020598020395893 15558595515189431064412115)
      ·
        refine ⟨23337893272784146596618173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15558595515189431064412115 23337893272784146596618173)
        ·
          refine ⟨8751709977294054973731815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23337893272784146596618173 8751709977294054973731815)
          ·
            refine ⟨13127564965941082460597723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8751709977294054973731815 13127564965941082460597723)
            ·
              refine ⟨19691347448911623690896585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13127564965941082460597723 19691347448911623690896585)
              ·
                refine ⟨14768510586683717768172439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19691347448911623690896585 14768510586683717768172439)
                ·
                  refine ⟨22152765880025576652258659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14768510586683717768172439 22152765880025576652258659)
                  ·
                    refine ⟨33229148820038364978387989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22152765880025576652258659 33229148820038364978387989)
                    ·
                      refine ⟨1557616350939298358361937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 33229148820038364978387989 1557616350939298358361937)
                      ·
                        rfl

theorem cell23_3033447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 1, 2, 1, 1, 6].length) (baseStart_3033447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3033447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3033447 prefixEnd_3033447 := by exact prefixLift 3033447
  have htrace : WordTrace (prefixWord ++ tailWord_3033447) baseStart_3033447 baseEnd_3033447 := by
    simpa [prefixWord, tailWord_3033447, baseEnd_3033447] using wordTrace_append hprefix tailTrace_3033447
  have hstable : (prefixWord ++ tailWord_3033447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3033447).length < 2 ^ (prefixWord ++ tailWord_3033447).sum := by decide
  have hdescent : baseEnd_3033447 < baseStart_3033447 := by decide
  rcases family_descends (prefixWord ++ tailWord_3033447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3033461 : List Nat := [1, 3, 4, 1, 2, 2, 1, 3, 2, 4]
def baseStart_3033461 : Nat := 118140960795 + 3033461 * 2 ^ 59
def prefixEnd_3033461 : Nat := 4983230072969 + 3 ^ 40 * 3033461 * 2
def baseEnd_3033461 : Nat := 519207846556153767862291

theorem tailTrace_3033461 : CollatzResearch.WordTrace tailWord_3033461 prefixEnd_3033461 519207846556153767862291 := by
  unfold tailWord_3033461
  simp only [CollatzResearch.WordTrace]
  refine ⟨110639412063296345737940237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73759608042197563825293491 110639412063296345737940237)
  ·
    refine ⟨41489779523736129651727589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 110639412063296345737940237 41489779523736129651727589)
    ·
      refine ⟨7779333660700524309698923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 41489779523736129651727589 7779333660700524309698923)
      ·
        refine ⟨11669000491050786464548385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7779333660700524309698923 11669000491050786464548385)
        ·
          refine ⟨8751750368288089848411289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11669000491050786464548385 8751750368288089848411289)
          ·
            refine ⟨6563812776216067386308467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8751750368288089848411289 6563812776216067386308467)
            ·
              refine ⟨9845719164324101079462701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6563812776216067386308467 9845719164324101079462701)
              ·
                refine ⟨3692144686621537904798513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9845719164324101079462701 3692144686621537904798513)
                ·
                  refine ⟨2769108514966153428598885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3692144686621537904798513 2769108514966153428598885)
                  ·
                    refine ⟨519207846556153767862291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2769108514966153428598885 519207846556153767862291)
                    ·
                      rfl

theorem cell23_3033461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 1, 3, 2, 4].length) (baseStart_3033461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3033461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3033461 prefixEnd_3033461 := by exact prefixLift 3033461
  have htrace : WordTrace (prefixWord ++ tailWord_3033461) baseStart_3033461 baseEnd_3033461 := by
    simpa [prefixWord, tailWord_3033461, baseEnd_3033461] using wordTrace_append hprefix tailTrace_3033461
  have hstable : (prefixWord ++ tailWord_3033461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3033461).length < 2 ^ (prefixWord ++ tailWord_3033461).sum := by decide
  have hdescent : baseEnd_3033461 < baseStart_3033461 := by decide
  rcases family_descends (prefixWord ++ tailWord_3033461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3033484 : List Nat := [2, 2, 1, 2, 1, 5, 1, 2, 1, 3, 3]
def baseStart_3033484 : Nat := 118140960795 + 3033484 * 2 ^ 59
def prefixEnd_3033484 : Nat := 4983230072969 + 3 ^ 40 * 3033484 * 2
def baseEnd_3033484 : Nat := 1557635349723514713599267

theorem tailTrace_3033484 : CollatzResearch.WordTrace tailWord_3033484 prefixEnd_3033484 1557635349723514713599267 := by
  unfold tailWord_3033484
  simp only [CollatzResearch.WordTrace]
  refine ⟨55320125471106510333013753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73760167294808680444018337 55320125471106510333013753)
  ·
    refine ⟨41490094103329882749760315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55320125471106510333013753 41490094103329882749760315)
    ·
      refine ⟨62235141154994824124640473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41490094103329882749760315 62235141154994824124640473)
      ·
        refine ⟨46676355866246118093480355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62235141154994824124640473 46676355866246118093480355)
        ·
          refine ⟨70014533799369177140220533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46676355866246118093480355 70014533799369177140220533)
          ·
            refine ⟨6563862543690860356895675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 70014533799369177140220533 6563862543690860356895675)
            ·
              refine ⟨9845793815536290535343513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6563862543690860356895675 9845793815536290535343513)
              ·
                refine ⟨7384345361652217901507635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9845793815536290535343513 7384345361652217901507635)
                ·
                  refine ⟨11076518042478326852261453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7384345361652217901507635 11076518042478326852261453)
                  ·
                    refine ⟨4153694265929372569598045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11076518042478326852261453 4153694265929372569598045)
                    ·
                      refine ⟨1557635349723514713599267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4153694265929372569598045 1557635349723514713599267)
                      ·
                        rfl

theorem cell23_3033484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 1, 2, 1, 3, 3].length) (baseStart_3033484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3033484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3033484 prefixEnd_3033484 := by exact prefixLift 3033484
  have htrace : WordTrace (prefixWord ++ tailWord_3033484) baseStart_3033484 baseEnd_3033484 := by
    simpa [prefixWord, tailWord_3033484, baseEnd_3033484] using wordTrace_append hprefix tailTrace_3033484
  have hstable : (prefixWord ++ tailWord_3033484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3033484).length < 2 ^ (prefixWord ++ tailWord_3033484).sum := by decide
  have hdescent : baseEnd_3033484 < baseStart_3033484 := by decide
  rcases family_descends (prefixWord ++ tailWord_3033484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3033502 : List Nat := [4, 3, 1, 2, 1, 2, 1, 4, 1, 2, 2]
def baseStart_3033502 : Nat := 118140960795 + 3033502 * 2 ^ 59
def prefixEnd_3033502 : Nat := 4983230072969 + 3 ^ 40 * 3033502 * 2
def baseEnd_3033502 : Nat := 1557644592375295643174185

theorem tailTrace_3033502 : CollatzResearch.WordTrace tailWord_3033502 prefixEnd_3033502 1557644592375295643174185 := by
  unfold tailWord_3033502
  simp only [CollatzResearch.WordTrace]
  refine ⟨13830113432018476217522845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 73760604970765206493455173 13830113432018476217522845)
  ·
    refine ⟨5186292537006928581571067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13830113432018476217522845 5186292537006928581571067)
    ·
      refine ⟨7779438805510392872356601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5186292537006928581571067 7779438805510392872356601)
      ·
        refine ⟨5834579104132794654267451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7779438805510392872356601 5834579104132794654267451)
        ·
          refine ⟨8751868656199191981401177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5834579104132794654267451 8751868656199191981401177)
          ·
            refine ⟨6563901492149393986050883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8751868656199191981401177 6563901492149393986050883)
            ·
              refine ⟨9845852238224090979076325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6563901492149393986050883 9845852238224090979076325)
              ·
                refine ⟨1846097294667017058576811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9845852238224090979076325 1846097294667017058576811)
                ·
                  refine ⟨2769145942000525587865217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1846097294667017058576811 2769145942000525587865217)
                  ·
                    refine ⟨2076859456500394190898913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2769145942000525587865217 2076859456500394190898913)
                    ·
                      refine ⟨1557644592375295643174185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2076859456500394190898913 1557644592375295643174185)
                      ·
                        rfl

theorem cell23_3033502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 1, 4, 1, 2, 2].length) (baseStart_3033502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3033502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3033502 prefixEnd_3033502 := by exact prefixLift 3033502
  have htrace : WordTrace (prefixWord ++ tailWord_3033502) baseStart_3033502 baseEnd_3033502 := by
    simpa [prefixWord, tailWord_3033502, baseEnd_3033502] using wordTrace_append hprefix tailTrace_3033502
  have hstable : (prefixWord ++ tailWord_3033502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3033502).length < 2 ^ (prefixWord ++ tailWord_3033502).sum := by decide
  have hdescent : baseEnd_3033502 < baseStart_3033502 := by decide
  rcases family_descends (prefixWord ++ tailWord_3033502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3033507 : List Nat := [1, 1, 1, 4, 1, 4, 1, 1, 2, 3, 4]
def baseStart_3033507 : Nat := 118140960795 + 3033507 * 2 ^ 59
def prefixEnd_3033507 : Nat := 4983230072969 + 3 ^ 40 * 3033507 * 2
def baseEnd_3033507 : Nat := 1557647159778568123611661

theorem tailTrace_3033507 : CollatzResearch.WordTrace tailWord_3033507 prefixEnd_3033507 1557647159778568123611661 := by
  unfold tailWord_3033507
  simp only [CollatzResearch.WordTrace]
  refine ⟨110641089821129695594114775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73760726547419797062743183 110641089821129695594114775)
  ·
    refine ⟨165961634731694543391172163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110641089821129695594114775 165961634731694543391172163)
    ·
      refine ⟨248942452097541815086758245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165961634731694543391172163 248942452097541815086758245)
      ·
        refine ⟨46676709768289090328767171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 248942452097541815086758245 46676709768289090328767171)
        ·
          refine ⟨70015064652433635493150757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46676709768289090328767171 70015064652433635493150757)
          ·
            refine ⟨13127824622331306654965767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 70015064652433635493150757 13127824622331306654965767)
            ·
              refine ⟨19691736933496959982448651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13127824622331306654965767 19691736933496959982448651)
              ·
                refine ⟨29537605400245439973672977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19691736933496959982448651 29537605400245439973672977)
                ·
                  refine ⟨22153204050184079980254733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29537605400245439973672977 22153204050184079980254733)
                  ·
                    refine ⟨8307451518819029992595525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22153204050184079980254733 8307451518819029992595525)
                    ·
                      refine ⟨1557647159778568123611661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8307451518819029992595525 1557647159778568123611661)
                      ·
                        rfl

theorem cell23_3033507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 1, 1, 2, 3, 4].length) (baseStart_3033507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3033507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3033507 prefixEnd_3033507 := by exact prefixLift 3033507
  have htrace : WordTrace (prefixWord ++ tailWord_3033507) baseStart_3033507 baseEnd_3033507 := by
    simpa [prefixWord, tailWord_3033507, baseEnd_3033507] using wordTrace_append hprefix tailTrace_3033507
  have hstable : (prefixWord ++ tailWord_3033507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3033507).length < 2 ^ (prefixWord ++ tailWord_3033507).sum := by decide
  have hdescent : baseEnd_3033507 < baseStart_3033507 := by decide
  rcases family_descends (prefixWord ++ tailWord_3033507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3033511 : List Nat := [1, 1, 6, 1, 1, 2, 1, 2, 3, 3, 2]
def baseStart_3033511 : Nat := 118140960795 + 3033511 * 2 ^ 59
def prefixEnd_3033511 : Nat := 4983230072969 + 3 ^ 40 * 3033511 * 2
def baseEnd_3033511 : Nat := 1557649213701186107961643

theorem tailTrace_3033511 : CollatzResearch.WordTrace tailWord_3033511 prefixEnd_3033511 1557649213701186107961643 := by
  unfold tailWord_3033511
  simp only [CollatzResearch.WordTrace]
  refine ⟨110641235713115204277260387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73760823808743469518173591 110641235713115204277260387)
  ·
    refine ⟨165961853569672806415890581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110641235713115204277260387 165961853569672806415890581)
    ·
      refine ⟨7779461886078412800744871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 165961853569672806415890581 7779461886078412800744871)
      ·
        refine ⟨11669192829117619201117307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7779461886078412800744871 11669192829117619201117307)
        ·
          refine ⟨17503789243676428801675961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11669192829117619201117307 17503789243676428801675961)
          ·
            refine ⟨13127841932757321601256971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17503789243676428801675961 13127841932757321601256971)
            ·
              refine ⟨19691762899135982401885457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13127841932757321601256971 19691762899135982401885457)
              ·
                refine ⟨14768822174351986801414093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19691762899135982401885457 14768822174351986801414093)
                ·
                  refine ⟨5538308315381995050530285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14768822174351986801414093 5538308315381995050530285)
                  ·
                    refine ⟨2076865618268248143948857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5538308315381995050530285 2076865618268248143948857)
                    ·
                      refine ⟨1557649213701186107961643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2076865618268248143948857 1557649213701186107961643)
                      ·
                        rfl

theorem cell23_3033511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 1, 2, 3, 3, 2].length) (baseStart_3033511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3033511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3033511 prefixEnd_3033511 := by exact prefixLift 3033511
  have htrace : WordTrace (prefixWord ++ tailWord_3033511) baseStart_3033511 baseEnd_3033511 := by
    simpa [prefixWord, tailWord_3033511, baseEnd_3033511] using wordTrace_append hprefix tailTrace_3033511
  have hstable : (prefixWord ++ tailWord_3033511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3033511).length < 2 ^ (prefixWord ++ tailWord_3033511).sum := by decide
  have hdescent : baseEnd_3033511 < baseStart_3033511 := by decide
  rcases family_descends (prefixWord ++ tailWord_3033511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3033575 : List Nat := [1, 1, 5, 2, 1, 1, 5, 1, 2, 2, 2]
def baseStart_3033575 : Nat := 118140960795 + 3033575 * 2 ^ 59
def prefixEnd_3033575 : Nat := 4983230072969 + 3 ^ 40 * 3033575 * 2
def baseEnd_3033575 : Nat := 1557682076463073857561349

theorem tailTrace_3033575 : CollatzResearch.WordTrace tailWord_3033575 prefixEnd_3033575 1557682076463073857561349 := by
  unfold tailWord_3033575
  simp only [CollatzResearch.WordTrace]
  refine ⟨110643569984883343207590179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73762379989922228805060119 110643569984883343207590179)
  ·
    refine ⟨165965354977325014811385269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110643569984883343207590179 165965354977325014811385269)
    ·
      refine ⟨15559252029124220138567369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 165965354977325014811385269 15559252029124220138567369)
      ·
        refine ⟨11669439021843165103925527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15559252029124220138567369 11669439021843165103925527)
        ·
          refine ⟨17504158532764747655888291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11669439021843165103925527 17504158532764747655888291)
          ·
            refine ⟨26256237799147121483832437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17504158532764747655888291 26256237799147121483832437)
            ·
              refine ⟨2461522293670042639109291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 26256237799147121483832437 2461522293670042639109291)
              ·
                refine ⟨3692283440505063958663937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2461522293670042639109291 3692283440505063958663937)
                ·
                  refine ⟨2769212580378797968997953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3692283440505063958663937 2769212580378797968997953)
                  ·
                    refine ⟨2076909435284098476748465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2769212580378797968997953 2076909435284098476748465)
                    ·
                      refine ⟨1557682076463073857561349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2076909435284098476748465 1557682076463073857561349)
                      ·
                        rfl

theorem cell23_3033575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 5, 1, 2, 2, 2].length) (baseStart_3033575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3033575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3033575 prefixEnd_3033575 := by exact prefixLift 3033575
  have htrace : WordTrace (prefixWord ++ tailWord_3033575) baseStart_3033575 baseEnd_3033575 := by
    simpa [prefixWord, tailWord_3033575, baseEnd_3033575] using wordTrace_append hprefix tailTrace_3033575
  have hstable : (prefixWord ++ tailWord_3033575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3033575).length < 2 ^ (prefixWord ++ tailWord_3033575).sum := by decide
  have hdescent : baseEnd_3033575 < baseStart_3033575 := by decide
  rcases family_descends (prefixWord ++ tailWord_3033575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3033577 : List Nat := [1, 2, 1, 1, 1, 2, 1, 3, 6, 5]
def baseStart_3033577 : Nat := 118140960795 + 3033577 * 2 ^ 59
def prefixEnd_3033577 : Nat := 4983230072969 + 3 ^ 40 * 3033577 * 2
def baseEnd_3033577 : Nat := 519227701141460949912113

theorem tailTrace_3033577 : CollatzResearch.WordTrace tailWord_3033577 prefixEnd_3033577 519227701141460949912113 := by
  unfold tailWord_3033577
  simp only [CollatzResearch.WordTrace]
  refine ⟨110643642930876097549162985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73762428620584065032775323 110643642930876097549162985)
  ·
    refine ⟨82982732198157073161872239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110643642930876097549162985 82982732198157073161872239)
    ·
      refine ⟨124474098297235609742808359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82982732198157073161872239 124474098297235609742808359)
      ·
        refine ⟨186711147445853414614212539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124474098297235609742808359 186711147445853414614212539)
        ·
          refine ⟨280066721168780121921318809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 186711147445853414614212539 280066721168780121921318809)
          ·
            refine ⟨210050040876585091440989107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 280066721168780121921318809 210050040876585091440989107)
            ·
              refine ⟨315075061314877637161483661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 210050040876585091440989107 315075061314877637161483661)
              ·
                refine ⟨118153147993079113935556373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 315075061314877637161483661 118153147993079113935556373)
                ·
                  refine ⟨5538428812175583465729205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 118153147993079113935556373 5538428812175583465729205)
                  ·
                    refine ⟨519227701141460949912113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5538428812175583465729205 519227701141460949912113)
                    ·
                      rfl

theorem cell23_3033577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 3, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 3, 6, 5].length) (baseStart_3033577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3033577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3033577 prefixEnd_3033577 := by exact prefixLift 3033577
  have htrace : WordTrace (prefixWord ++ tailWord_3033577) baseStart_3033577 baseEnd_3033577 := by
    simpa [prefixWord, tailWord_3033577, baseEnd_3033577] using wordTrace_append hprefix tailTrace_3033577
  have hstable : (prefixWord ++ tailWord_3033577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3033577).length < 2 ^ (prefixWord ++ tailWord_3033577).sum := by decide
  have hdescent : baseEnd_3033577 < baseStart_3033577 := by decide
  rcases family_descends (prefixWord ++ tailWord_3033577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3033617 : List Nat := [1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 5]
def baseStart_3033617 : Nat := 118140960795 + 3033617 * 2 ^ 59
def prefixEnd_3033617 : Nat := 4983230072969 + 3 ^ 40 * 3033617 * 2
def baseEnd_3033617 : Nat := 1557703642650562693236155

theorem tailTrace_3033617 : CollatzResearch.WordTrace tailWord_3033617 prefixEnd_3033617 1557703642650562693236155 := by
  unfold tailWord_3033617
  simp only [CollatzResearch.WordTrace]
  refine ⟨110645101850731184380619105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73763401233820789587079403 110645101850731184380619105)
  ·
    refine ⟨82983826388048388285464329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110645101850731184380619105 82983826388048388285464329)
    ·
      refine ⟨62237869791036291214098247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82983826388048388285464329 62237869791036291214098247)
      ·
        refine ⟨93356804686554436821147371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62237869791036291214098247 93356804686554436821147371)
        ·
          refine ⟨140035207029831655231721057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93356804686554436821147371 140035207029831655231721057)
          ·
            refine ⟨105026405272373741423790793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 140035207029831655231721057 105026405272373741423790793)
            ·
              refine ⟨78769803954280306067843095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 105026405272373741423790793 78769803954280306067843095)
              ·
                refine ⟨118154705931420459101764643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 78769803954280306067843095 118154705931420459101764643)
                ·
                  refine ⟨177232058897130688652646965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 118154705931420459101764643 177232058897130688652646965)
                  ·
                    refine ⟨16615505521606002061185653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 177232058897130688652646965 16615505521606002061185653)
                    ·
                      refine ⟨1557703642650562693236155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16615505521606002061185653 1557703642650562693236155)
                      ·
                        rfl

theorem cell23_3033617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 5].length) (baseStart_3033617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3033617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3033617 prefixEnd_3033617 := by exact prefixLift 3033617
  have htrace : WordTrace (prefixWord ++ tailWord_3033617) baseStart_3033617 baseEnd_3033617 := by
    simpa [prefixWord, tailWord_3033617, baseEnd_3033617] using wordTrace_append hprefix tailTrace_3033617
  have hstable : (prefixWord ++ tailWord_3033617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3033617).length < 2 ^ (prefixWord ++ tailWord_3033617).sum := by decide
  have hdescent : baseEnd_3033617 < baseStart_3033617 := by decide
  rcases family_descends (prefixWord ++ tailWord_3033617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3033651 : List Nat := [1, 1, 1, 2, 4, 2, 4, 1, 2, 2, 3]
def baseStart_3033651 : Nat := 118140960795 + 3033651 * 2 ^ 59
def prefixEnd_3033651 : Nat := 4983230072969 + 3 ^ 40 * 3033651 * 2
def baseEnd_3033651 : Nat := 1557721100992815560210999

theorem tailTrace_3033651 : CollatzResearch.WordTrace tailWord_3033651 prefixEnd_3033651 1557721100992815560210999 := by
  unfold tailWord_3033651
  simp only [CollatzResearch.WordTrace]
  refine ⟨110646341932608008187356807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73764227955072005458237871 110646341932608008187356807)
  ·
    refine ⟨165969512898912012281035211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110646341932608008187356807 165969512898912012281035211)
    ·
      refine ⟨248954269348368018421552817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165969512898912012281035211 248954269348368018421552817)
      ·
        refine ⟨186715702011276013816164613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 248954269348368018421552817 186715702011276013816164613)
        ·
          refine ⟨35009194127114252590530865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 186715702011276013816164613 35009194127114252590530865)
          ·
            refine ⟨26256895595335689442898149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35009194127114252590530865 26256895595335689442898149)
            ·
              refine ⟨4923167924125441770543403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26256895595335689442898149 4923167924125441770543403)
              ·
                refine ⟨7384751886188162655815105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4923167924125441770543403 7384751886188162655815105)
                ·
                  refine ⟨5538563914641121991861329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7384751886188162655815105 5538563914641121991861329)
                  ·
                    refine ⟨4153922935980841493895997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5538563914641121991861329 4153922935980841493895997)
                    ·
                      refine ⟨1557721100992815560210999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4153922935980841493895997 1557721100992815560210999)
                      ·
                        rfl

theorem cell23_3033651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 4, 1, 2, 2, 3].length) (baseStart_3033651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3033651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3033651 prefixEnd_3033651 := by exact prefixLift 3033651
  have htrace : WordTrace (prefixWord ++ tailWord_3033651) baseStart_3033651 baseEnd_3033651 := by
    simpa [prefixWord, tailWord_3033651, baseEnd_3033651] using wordTrace_append hprefix tailTrace_3033651
  have hstable : (prefixWord ++ tailWord_3033651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3033651).length < 2 ^ (prefixWord ++ tailWord_3033651).sum := by decide
  have hdescent : baseEnd_3033651 < baseStart_3033651 := by decide
  rcases family_descends (prefixWord ++ tailWord_3033651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
