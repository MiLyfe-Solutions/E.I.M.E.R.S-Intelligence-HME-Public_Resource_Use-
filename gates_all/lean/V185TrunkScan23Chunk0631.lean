import V185TrunkScan23Chunk0630

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_3731829 : List Nat := [1, 3, 4, 1, 2, 1, 1, 3, 1, 4, 2]
def baseStart_3731829 : Nat := 118140960795 + 3731829 * 2 ^ 59
def prefixEnd_3731829 : Nat := 4983230072969 + 3 ^ 40 * 3731829 * 2
def baseEnd_3731829 : Nat := 1916221997387584935575137

theorem tailTrace_3731829 : CollatzResearch.WordTrace tailWord_3731829 prefixEnd_3731829 1916221997387584935575137 := by
  unfold tailWord_3731829
  simp only [CollatzResearch.WordTrace]
  refine ⟨136110985597228353496630541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90740657064818902331087027 136110985597228353496630541)
  ·
    refine ⟨51041619598960632561236453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 136110985597228353496630541 51041619598960632561236453)
    ·
      refine ⟨9570303674805118605231835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 51041619598960632561236453 9570303674805118605231835)
      ·
        refine ⟨14355455512207677907847753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9570303674805118605231835 14355455512207677907847753)
        ·
          refine ⟨10766591634155758430885815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14355455512207677907847753 10766591634155758430885815)
          ·
            refine ⟨16149887451233637646328723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10766591634155758430885815 16149887451233637646328723)
            ·
              refine ⟨24224831176850456469493085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16149887451233637646328723 24224831176850456469493085)
              ·
                refine ⟨9084311691318921176059907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24224831176850456469493085 9084311691318921176059907)
                ·
                  refine ⟨13626467536978381764089861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9084311691318921176059907 13626467536978381764089861)
                  ·
                    refine ⟨2554962663183446580766849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13626467536978381764089861 2554962663183446580766849)
                    ·
                      refine ⟨1916221997387584935575137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2554962663183446580766849 1916221997387584935575137)
                      ·
                        rfl

theorem cell23_3731829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 1, 3, 1, 4, 2].length) (baseStart_3731829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3731829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3731829 prefixEnd_3731829 := by exact prefixLift 3731829
  have htrace : WordTrace (prefixWord ++ tailWord_3731829) baseStart_3731829 baseEnd_3731829 := by
    simpa [prefixWord, tailWord_3731829, baseEnd_3731829] using wordTrace_append hprefix tailTrace_3731829
  have hstable : (prefixWord ++ tailWord_3731829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3731829).length < 2 ^ (prefixWord ++ tailWord_3731829).sum := by decide
  have hdescent : baseEnd_3731829 < baseStart_3731829 := by decide
  rcases family_descends (prefixWord ++ tailWord_3731829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3731835 : List Nat := [1, 1, 1, 1, 1, 8, 1, 2, 7]
def baseStart_3731835 : Nat := 118140960795 + 3731835 * 2 ^ 59
def prefixEnd_3731835 : Nat := 4983230072969 + 3 ^ 40 * 3731835 * 2
def baseEnd_3731835 : Nat := 212913897585723545788901

theorem tailTrace_3731835 : CollatzResearch.WordTrace tailWord_3731835 prefixEnd_3731835 212913897585723545788901 := by
  unfold tailWord_3731835
  simp only [CollatzResearch.WordTrace]
  refine ⟨136111204435206616521348959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90740802956804411014232639 136111204435206616521348959)
  ·
    refine ⟨204166806652809924782023439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136111204435206616521348959 204166806652809924782023439)
    ·
      refine ⟨306250209979214887173035159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204166806652809924782023439 306250209979214887173035159)
      ·
        refine ⟨459375314968822330759552739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 306250209979214887173035159 459375314968822330759552739)
        ·
          refine ⟨689062972453233496139329109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 459375314968822330759552739 689062972453233496139329109)
          ·
            refine ⟨8074956708436330032882763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 689062972453233496139329109 8074956708436330032882763)
            ·
              refine ⟨12112435062654495049324145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8074956708436330032882763 12112435062654495049324145)
              ·
                refine ⟨9084326296990871286993109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12112435062654495049324145 9084326296990871286993109)
                ·
                  refine ⟨212913897585723545788901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9084326296990871286993109 212913897585723545788901)
                  ·
                    rfl

theorem cell23_3731835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 1, 2, 7].length) (baseStart_3731835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3731835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3731835 prefixEnd_3731835 := by exact prefixLift 3731835
  have htrace : WordTrace (prefixWord ++ tailWord_3731835) baseStart_3731835 baseEnd_3731835 := by
    simpa [prefixWord, tailWord_3731835, baseEnd_3731835] using wordTrace_append hprefix tailTrace_3731835
  have hstable : (prefixWord ++ tailWord_3731835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3731835).length < 2 ^ (prefixWord ++ tailWord_3731835).sum := by decide
  have hdescent : baseEnd_3731835 < baseStart_3731835 := by decide
  rcases family_descends (prefixWord ++ tailWord_3731835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3731845 : List Nat := [1, 3, 1, 1, 3, 1, 1, 1, 3, 5, 3]
def baseStart_3731845 : Nat := 118140960795 + 3731845 * 2 ^ 59
def prefixEnd_3731845 : Nat := 4983230072969 + 3 ^ 40 * 3731845 * 2
def baseEnd_3731845 : Nat := 1916230213078056872975063

theorem tailTrace_3731845 : CollatzResearch.WordTrace tailWord_3731845 prefixEnd_3731845 1916230213078056872975063 := by
  unfold tailWord_3731845
  simp only [CollatzResearch.WordTrace]
  refine ⟨136111569165170388229212989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90741046110113592152808659 136111569165170388229212989)
  ·
    refine ⟨51041838436938895585954871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 136111569165170388229212989 51041838436938895585954871)
    ·
      refine ⟨76562757655408343378932307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51041838436938895585954871 76562757655408343378932307)
      ·
        refine ⟨114844136483112515068398461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76562757655408343378932307 114844136483112515068398461)
        ·
          refine ⟨43066551181167193150649423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 114844136483112515068398461 43066551181167193150649423)
          ·
            refine ⟨64599826771750789725974135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43066551181167193150649423 64599826771750789725974135)
            ·
              refine ⟨96899740157626184588961203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64599826771750789725974135 96899740157626184588961203)
              ·
                refine ⟨145349610236439276883441805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 96899740157626184588961203 145349610236439276883441805)
                ·
                  refine ⟨54506103838664728831290677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 145349610236439276883441805 54506103838664728831290677)
                  ·
                    refine ⟨5109947234874818327933501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 54506103838664728831290677 5109947234874818327933501)
                    ·
                      refine ⟨1916230213078056872975063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5109947234874818327933501 1916230213078056872975063)
                      ·
                        rfl

theorem cell23_3731845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 1, 3, 5, 3].length) (baseStart_3731845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3731845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3731845 prefixEnd_3731845 := by exact prefixLift 3731845
  have htrace : WordTrace (prefixWord ++ tailWord_3731845) baseStart_3731845 baseEnd_3731845 := by
    simpa [prefixWord, tailWord_3731845, baseEnd_3731845] using wordTrace_append hprefix tailTrace_3731845
  have hstable : (prefixWord ++ tailWord_3731845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3731845).length < 2 ^ (prefixWord ++ tailWord_3731845).sum := by decide
  have hdescent : baseEnd_3731845 < baseStart_3731845 := by decide
  rcases family_descends (prefixWord ++ tailWord_3731845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3731850 : List Nat := [3, 1, 2, 5, 1, 2, 2, 1, 1, 3, 2]
def baseStart_3731850 : Nat := 118140960795 + 3731850 * 2 ^ 59
def prefixEnd_3731850 : Nat := 4983230072969 + 3 ^ 40 * 3731850 * 2
def baseEnd_3731850 : Nat := 1916232780481329353412541

theorem tailTrace_3731850 : CollatzResearch.WordTrace tailWord_3731850 prefixEnd_3731850 1916232780481329353412541 := by
  unfold tailWord_3731850
  simp only [CollatzResearch.WordTrace]
  refine ⟨34027937882538068520786251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90741167686768182722096669 34027937882538068520786251)
  ·
    refine ⟨51041906823807102781179377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34027937882538068520786251 51041906823807102781179377)
    ·
      refine ⟨38281430117855327085884533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51041906823807102781179377 38281430117855327085884533)
      ·
        refine ⟨3588884073548936914301675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 38281430117855327085884533 3588884073548936914301675)
        ·
          refine ⟨5383326110323405371452513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3588884073548936914301675 5383326110323405371452513)
          ·
            refine ⟨4037494582742554028589385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5383326110323405371452513 4037494582742554028589385)
            ·
              refine ⟨3028120937056915521442039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4037494582742554028589385 3028120937056915521442039)
              ·
                refine ⟨4542181405585373282163059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3028120937056915521442039 4542181405585373282163059)
                ·
                  refine ⟨6813272108378059923244589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4542181405585373282163059 6813272108378059923244589)
                  ·
                    refine ⟨2554977040641772471216721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6813272108378059923244589 2554977040641772471216721)
                    ·
                      refine ⟨1916232780481329353412541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2554977040641772471216721 1916232780481329353412541)
                      ·
                        rfl

theorem cell23_3731850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 2, 2, 1, 1, 3, 2].length) (baseStart_3731850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3731850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3731850 prefixEnd_3731850 := by exact prefixLift 3731850
  have htrace : WordTrace (prefixWord ++ tailWord_3731850) baseStart_3731850 baseEnd_3731850 := by
    simpa [prefixWord, tailWord_3731850, baseEnd_3731850] using wordTrace_append hprefix tailTrace_3731850
  have hstable : (prefixWord ++ tailWord_3731850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3731850).length < 2 ^ (prefixWord ++ tailWord_3731850).sum := by decide
  have hdescent : baseEnd_3731850 < baseStart_3731850 := by decide
  rcases family_descends (prefixWord ++ tailWord_3731850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3731852 : List Nat := [2, 2, 1, 2, 1, 4, 1, 5, 5]
def baseStart_3731852 : Nat := 118140960795 + 3731852 * 2 ^ 59
def prefixEnd_3731852 : Nat := 4983230072969 + 3 ^ 40 * 3731852 * 2
def baseEnd_3731852 : Nat := 212914867493626482843059

theorem tailTrace_3731852 : CollatzResearch.WordTrace tailWord_3731852 prefixEnd_3731852 212914867493626482843059 := by
  unfold tailWord_3731852
  simp only [CollatzResearch.WordTrace]
  refine ⟨68055912238072514212358905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90741216317430018949811873 68055912238072514212358905)
  ·
    refine ⟨51041934178554385659269179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68055912238072514212358905 51041934178554385659269179)
    ·
      refine ⟨76562901267831578488903769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51041934178554385659269179 76562901267831578488903769)
      ·
        refine ⟨57422175950873683866677827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76562901267831578488903769 57422175950873683866677827)
        ·
          refine ⟨86133263926310525800016741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57422175950873683866677827 86133263926310525800016741)
          ·
            refine ⟨16149986986183223587503139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 86133263926310525800016741 16149986986183223587503139)
            ·
              refine ⟨24224980479274835381254709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16149986986183223587503139 24224980479274835381254709)
              ·
                refine ⟨2271091919932015816992629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24224980479274835381254709 2271091919932015816992629)
                ·
                  refine ⟨212914867493626482843059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2271091919932015816992629 212914867493626482843059)
                  ·
                    rfl

theorem cell23_3731852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 1, 5, 5].length) (baseStart_3731852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3731852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3731852 prefixEnd_3731852 := by exact prefixLift 3731852
  have htrace : WordTrace (prefixWord ++ tailWord_3731852) baseStart_3731852 baseEnd_3731852 := by
    simpa [prefixWord, tailWord_3731852, baseEnd_3731852] using wordTrace_append hprefix tailTrace_3731852
  have hstable : (prefixWord ++ tailWord_3731852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3731852).length < 2 ^ (prefixWord ++ tailWord_3731852).sum := by decide
  have hdescent : baseEnd_3731852 < baseStart_3731852 := by decide
  rcases family_descends (prefixWord ++ tailWord_3731852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3731865 : List Nat := [1, 2, 1, 2, 1, 4, 2, 1, 4, 5]
def baseStart_3731865 : Nat := 118140960795 + 3731865 * 2 ^ 59
def prefixEnd_3731865 : Nat := 4983230072969 + 3 ^ 40 * 3731865 * 2
def baseEnd_3731865 : Nat := 638746827563715598241657

theorem tailTrace_3731865 : CollatzResearch.WordTrace tailWord_3731865 prefixEnd_3731865 638746827563715598241657 := by
  unfold tailWord_3731865
  simp only [CollatzResearch.WordTrace]
  refine ⟨136112298625097931644941049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90741532416731954429960699 136112298625097931644941049)
  ·
    refine ⟨102084223968823448733705787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136112298625097931644941049 102084223968823448733705787)
    ·
      refine ⟨153126335953235173100558681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102084223968823448733705787 153126335953235173100558681)
      ·
        refine ⟨114844751964926379825419011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 153126335953235173100558681 114844751964926379825419011)
        ·
          refine ⟨172267127947389569738128517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114844751964926379825419011 172267127947389569738128517)
          ·
            refine ⟨32300086490135544325899097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 172267127947389569738128517 32300086490135544325899097)
            ·
              refine ⟨24225064867601658244424323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32300086490135544325899097 24225064867601658244424323)
              ·
                refine ⟨36337597301402487366636485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24225064867601658244424323 36337597301402487366636485)
                ·
                  refine ⟨6813299494012966381244341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36337597301402487366636485 6813299494012966381244341)
                  ·
                    refine ⟨638746827563715598241657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6813299494012966381244341 638746827563715598241657)
                    ·
                      rfl

theorem cell23_3731865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 2, 1, 4, 5].length) (baseStart_3731865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3731865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3731865 prefixEnd_3731865 := by exact prefixLift 3731865
  have htrace : WordTrace (prefixWord ++ tailWord_3731865) baseStart_3731865 baseEnd_3731865 := by
    simpa [prefixWord, tailWord_3731865, baseEnd_3731865] using wordTrace_append hprefix tailTrace_3731865
  have hstable : (prefixWord ++ tailWord_3731865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3731865).length < 2 ^ (prefixWord ++ tailWord_3731865).sum := by decide
  have hdescent : baseEnd_3731865 < baseStart_3731865 := by decide
  rcases family_descends (prefixWord ++ tailWord_3731865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3731880 : List Nat := [2, 1, 6, 1, 1, 2, 3, 1, 2, 2, 2]
def baseStart_3731880 : Nat := 118140960795 + 3731880 * 2 ^ 59
def prefixEnd_3731880 : Nat := 4983230072969 + 3 ^ 40 * 3731880 * 2
def baseEnd_3731880 : Nat := 1916248184900964236037403

theorem tailTrace_3731880 : CollatzResearch.WordTrace tailWord_3731880 prefixEnd_3731880 1916248184900964236037403 := by
  unfold tailWord_3731880
  simp only [CollatzResearch.WordTrace]
  refine ⟨68056422860021794603368547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90741897146695726137824729 68056422860021794603368547)
  ·
    refine ⟨102084634290032691905052821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68056422860021794603368547 102084634290032691905052821)
    ·
      refine ⟨4785217232345282433049351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 102084634290032691905052821 4785217232345282433049351)
      ·
        refine ⟨7177825848517923649574027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4785217232345282433049351 7177825848517923649574027)
        ·
          refine ⟨10766738772776885474361041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7177825848517923649574027 10766738772776885474361041)
          ·
            refine ⟨8075054079582664105770781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10766738772776885474361041 8075054079582664105770781)
            ·
              refine ⟨3028145279843499039664043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8075054079582664105770781 3028145279843499039664043)
              ·
                refine ⟨4542217919765248559496065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3028145279843499039664043 4542217919765248559496065)
                ·
                  refine ⟨3406663439823936419622049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4542217919765248559496065 3406663439823936419622049)
                  ·
                    refine ⟨2554997579867952314716537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3406663439823936419622049 2554997579867952314716537)
                    ·
                      refine ⟨1916248184900964236037403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2554997579867952314716537 1916248184900964236037403)
                      ·
                        rfl

theorem cell23_3731880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 3, 1, 2, 2, 2].length) (baseStart_3731880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3731880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3731880 prefixEnd_3731880 := by exact prefixLift 3731880
  have htrace : WordTrace (prefixWord ++ tailWord_3731880) baseStart_3731880 baseEnd_3731880 := by
    simpa [prefixWord, tailWord_3731880, baseEnd_3731880] using wordTrace_append hprefix tailTrace_3731880
  have hstable : (prefixWord ++ tailWord_3731880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3731880).length < 2 ^ (prefixWord ++ tailWord_3731880).sum := by decide
  have hdescent : baseEnd_3731880 < baseStart_3731880 := by decide
  rcases family_descends (prefixWord ++ tailWord_3731880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3731902 : List Nat := [4, 2, 1, 1, 1, 1, 4, 1, 1, 3, 4]
def baseStart_3731902 : Nat := 118140960795 + 3731902 * 2 ^ 59
def prefixEnd_3731902 : Nat := 4983230072969 + 3 ^ 40 * 3731902 * 2
def baseEnd_3731902 : Nat := 1916259481475363149962301

theorem tailTrace_3731902 : CollatzResearch.WordTrace tailWord_3731902 prefixEnd_3731902 1916259481475363149962301 := by
  unfold tailWord_3731902
  simp only [CollatzResearch.WordTrace]
  refine ⟨17014206015745485870504745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 90742432083975924642691973 17014206015745485870504745)
  ·
    refine ⟨12760654511809114402878559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17014206015745485870504745 12760654511809114402878559)
    ·
      refine ⟨19140981767713671604317839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12760654511809114402878559 19140981767713671604317839)
      ·
        refine ⟨28711472651570507406476759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19140981767713671604317839 28711472651570507406476759)
        ·
          refine ⟨43067208977355761109715139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28711472651570507406476759 43067208977355761109715139)
          ·
            refine ⟨64600813466033641664572709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43067208977355761109715139 64600813466033641664572709)
            ·
              refine ⟨12112652524881307812107383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 64600813466033641664572709 12112652524881307812107383)
              ·
                refine ⟨18168978787321961718161075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12112652524881307812107383 18168978787321961718161075)
                ·
                  refine ⟨27253468180982942577241613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18168978787321961718161075 27253468180982942577241613)
                  ·
                    refine ⟨10220050567868603466465605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27253468180982942577241613 10220050567868603466465605)
                    ·
                      refine ⟨1916259481475363149962301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10220050567868603466465605 1916259481475363149962301)
                      ·
                        rfl

theorem cell23_3731902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 4, 1, 1, 3, 4].length) (baseStart_3731902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3731902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3731902 prefixEnd_3731902 := by exact prefixLift 3731902
  have htrace : WordTrace (prefixWord ++ tailWord_3731902) baseStart_3731902 baseEnd_3731902 := by
    simpa [prefixWord, tailWord_3731902, baseEnd_3731902] using wordTrace_append hprefix tailTrace_3731902
  have hstable : (prefixWord ++ tailWord_3731902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3731902).length < 2 ^ (prefixWord ++ tailWord_3731902).sum := by decide
  have hdescent : baseEnd_3731902 < baseStart_3731902 := by decide
  rcases family_descends (prefixWord ++ tailWord_3731902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3732026 : List Nat := [3, 1, 1, 1, 3, 3, 4, 1, 1, 1, 4]
def baseStart_3732026 : Nat := 118140960795 + 3732026 * 2 ^ 59
def prefixEnd_3732026 : Nat := 4983230072969 + 3 ^ 40 * 3732026 * 2
def baseEnd_3732026 : Nat := 1916323153076520664811731

theorem tailTrace_3732026 : CollatzResearch.WordTrace tailWord_3732026 prefixEnd_3732026 1916323153076520664811731 := by
  unfold tailWord_3732026
  simp only [CollatzResearch.WordTrace]
  refine ⟨34029542694378664035387983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90745447185009770761034621 34029542694378664035387983)
  ·
    refine ⟨51044314041567996053081975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34029542694378664035387983 51044314041567996053081975)
    ·
      refine ⟨76566471062351994079622963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51044314041567996053081975 76566471062351994079622963)
      ·
        refine ⟨114849706593527991119434445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76566471062351994079622963 114849706593527991119434445)
        ·
          refine ⟨43068639972572996669787917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 114849706593527991119434445 43068639972572996669787917)
          ·
            refine ⟨16150739989714873751170469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43068639972572996669787917 16150739989714873751170469)
            ·
              refine ⟨3028263748071538828344463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16150739989714873751170469 3028263748071538828344463)
              ·
                refine ⟨4542395622107308242516695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3028263748071538828344463 4542395622107308242516695)
                ·
                  refine ⟨6813593433160962363775043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4542395622107308242516695 6813593433160962363775043)
                  ·
                    refine ⟨10220390149741443545662565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6813593433160962363775043 10220390149741443545662565)
                    ·
                      refine ⟨1916323153076520664811731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10220390149741443545662565 1916323153076520664811731)
                      ·
                        rfl

theorem cell23_3732026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 4, 1, 1, 1, 4].length) (baseStart_3732026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3732026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3732026 prefixEnd_3732026 := by exact prefixLift 3732026
  have htrace : WordTrace (prefixWord ++ tailWord_3732026) baseStart_3732026 baseEnd_3732026 := by
    simpa [prefixWord, tailWord_3732026, baseEnd_3732026] using wordTrace_append hprefix tailTrace_3732026
  have hstable : (prefixWord ++ tailWord_3732026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3732026).length < 2 ^ (prefixWord ++ tailWord_3732026).sum := by decide
  have hdescent : baseEnd_3732026 < baseStart_3732026 := by decide
  rcases family_descends (prefixWord ++ tailWord_3732026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3732043 : List Nat := [1, 1, 1, 1, 3, 1, 6, 4, 1, 2, 2]
def baseStart_3732043 : Nat := 118140960795 + 3732043 * 2 ^ 59
def prefixEnd_3732043 : Nat := 4983230072969 + 3 ^ 40 * 3732043 * 2
def baseEnd_3732043 : Nat := 1916331882247647098299153

theorem tailTrace_3732043 : CollatzResearch.WordTrace tailWord_3732043 prefixEnd_3732043 1916331882247647098299153 := by
  unfold tailWord_3732043
  simp only [CollatzResearch.WordTrace]
  refine ⟨136118790818453068044920783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90745860545635378696613855 136118790818453068044920783)
  ·
    refine ⟨204178186227679602067381175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136118790818453068044920783 204178186227679602067381175)
    ·
      refine ⟨306267279341519403101071763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204178186227679602067381175 306267279341519403101071763)
      ·
        refine ⟨459400919012279104651607645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 306267279341519403101071763 459400919012279104651607645)
        ·
          refine ⟨172275344629604664244352867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 459400919012279104651607645 172275344629604664244352867)
          ·
            refine ⟨258413016944406996366529301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 172275344629604664244352867 258413016944406996366529301)
            ·
              refine ⟨12113110169269077954681061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 258413016944406996366529301 12113110169269077954681061)
              ·
                refine ⟨2271208156737952116502699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12113110169269077954681061 2271208156737952116502699)
                ·
                  refine ⟨3406812235106928174754049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2271208156737952116502699 3406812235106928174754049)
                  ·
                    refine ⟨2555109176330196131065537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3406812235106928174754049 2555109176330196131065537)
                    ·
                      refine ⟨1916331882247647098299153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2555109176330196131065537 1916331882247647098299153)
                      ·
                        rfl

theorem cell23_3732043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 6, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 6, 4, 1, 2, 2].length) (baseStart_3732043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3732043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3732043 prefixEnd_3732043 := by exact prefixLift 3732043
  have htrace : WordTrace (prefixWord ++ tailWord_3732043) baseStart_3732043 baseEnd_3732043 := by
    simpa [prefixWord, tailWord_3732043, baseEnd_3732043] using wordTrace_append hprefix tailTrace_3732043
  have hstable : (prefixWord ++ tailWord_3732043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3732043).length < 2 ^ (prefixWord ++ tailWord_3732043).sum := by decide
  have hdescent : baseEnd_3732043 < baseStart_3732043 := by decide
  rcases family_descends (prefixWord ++ tailWord_3732043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3732066 : List Nat := [3, 3, 2, 3, 1, 1, 1, 9]
def baseStart_3732066 : Nat := 118140960795 + 3732066 * 2 ^ 59
def prefixEnd_3732066 : Nat := 4983230072969 + 3 ^ 40 * 3732066 * 2
def baseEnd_3732066 : Nat := 70975692307507426233761

theorem tailTrace_3732066 : CollatzResearch.WordTrace tailWord_3732066 prefixEnd_3732066 70975692307507426233761 := by
  unfold tailWord_3732066
  simp only [CollatzResearch.WordTrace]
  refine ⟨34029907424342435743252013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90746419798246495315338701 34029907424342435743252013)
  ·
    refine ⟨12761215284128413403719505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34029907424342435743252013 12761215284128413403719505)
    ·
      refine ⟨9570911463096310052789629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12761215284128413403719505 9570911463096310052789629)
      ·
        refine ⟨3589091798661116269796111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9570911463096310052789629 3589091798661116269796111)
        ·
          refine ⟨5383637697991674404694167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3589091798661116269796111 5383637697991674404694167)
          ·
            refine ⟨8075456546987511607041251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5383637697991674404694167 8075456546987511607041251)
            ·
              refine ⟨12113184820481267410561877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8075456546987511607041251 12113184820481267410561877)
              ·
                refine ⟨70975692307507426233761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 12113184820481267410561877 70975692307507426233761)
                ·
                  rfl

theorem cell23_3732066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 1, 9].length) (baseStart_3732066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3732066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3732066 prefixEnd_3732066 := by exact prefixLift 3732066
  have htrace : WordTrace (prefixWord ++ tailWord_3732066) baseStart_3732066 baseEnd_3732066 := by
    simpa [prefixWord, tailWord_3732066, baseEnd_3732066] using wordTrace_append hprefix tailTrace_3732066
  have hstable : (prefixWord ++ tailWord_3732066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3732066).length < 2 ^ (prefixWord ++ tailWord_3732066).sum := by decide
  have hdescent : baseEnd_3732066 < baseStart_3732066 := by decide
  rcases family_descends (prefixWord ++ tailWord_3732066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3732077 : List Nat := [1, 5, 1, 1, 3, 3, 1, 3, 1, 2, 2]
def baseStart_3732077 : Nat := 118140960795 + 3732077 * 2 ^ 59
def prefixEnd_3732077 : Nat := 4983230072969 + 3 ^ 40 * 3732077 * 2
def baseEnd_3732077 : Nat := 1916349340589899965273997

theorem tailTrace_3732077 : CollatzResearch.WordTrace tailWord_3732077 prefixEnd_3732077 1916349340589899965273997 := by
  unfold tailWord_3732077
  simp only [CollatzResearch.WordTrace]
  refine ⟨136120030900329891851658485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90746687266886594567772323 136120030900329891851658485)
  ·
    refine ⟨12761252896905927361092983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 136120030900329891851658485 12761252896905927361092983)
    ·
      refine ⟨19141879345358891041639475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12761252896905927361092983 19141879345358891041639475)
      ·
        refine ⟨28712819018038336562459213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19141879345358891041639475 28712819018038336562459213)
        ·
          refine ⟨10767307131764376210922205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28712819018038336562459213 10767307131764376210922205)
          ·
            refine ⟨4037740174411641079095827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10767307131764376210922205 4037740174411641079095827)
            ·
              refine ⟨6056610261617461618643741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4037740174411641079095827 6056610261617461618643741)
              ·
                refine ⟨2271228848106548106991403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6056610261617461618643741 2271228848106548106991403)
                ·
                  refine ⟨3406843272159822160487105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2271228848106548106991403 3406843272159822160487105)
                  ·
                    refine ⟨2555132454119866620365329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3406843272159822160487105 2555132454119866620365329)
                    ·
                      refine ⟨1916349340589899965273997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2555132454119866620365329 1916349340589899965273997)
                      ·
                        rfl

theorem cell23_3732077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 3, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 3, 1, 3, 1, 2, 2].length) (baseStart_3732077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3732077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3732077 prefixEnd_3732077 := by exact prefixLift 3732077
  have htrace : WordTrace (prefixWord ++ tailWord_3732077) baseStart_3732077 baseEnd_3732077 := by
    simpa [prefixWord, tailWord_3732077, baseEnd_3732077] using wordTrace_append hprefix tailTrace_3732077
  have hstable : (prefixWord ++ tailWord_3732077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3732077).length < 2 ^ (prefixWord ++ tailWord_3732077).sum := by decide
  have hdescent : baseEnd_3732077 < baseStart_3732077 := by decide
  rcases family_descends (prefixWord ++ tailWord_3732077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3732092 : List Nat := [2, 2, 2, 1, 1, 2, 2, 1, 4, 6]
def baseStart_3732092 : Nat := 118140960795 + 3732092 * 2 ^ 59
def prefixEnd_3732092 : Nat := 4983230072969 + 3 ^ 40 * 3732092 * 2
def baseEnd_3732092 : Nat := 638785680933239135528809

theorem tailTrace_3732092 : CollatzResearch.WordTrace tailWord_3732092 prefixEnd_3732092 638785680933239135528809 := by
  unfold tailWord_3732092
  simp only [CollatzResearch.WordTrace]
  refine ⟨68060288997637774706727265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90747051996850366275636353 68060288997637774706727265)
  ·
    refine ⟨51045216748228331030045449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68060288997637774706727265 51045216748228331030045449)
    ·
      refine ⟨38283912561171248272534087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51045216748228331030045449 38283912561171248272534087)
      ·
        refine ⟨57425868841756872408801131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38283912561171248272534087 57425868841756872408801131)
        ·
          refine ⟨86138803262635308613201697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57425868841756872408801131 86138803262635308613201697)
          ·
            refine ⟨64604102446976481459901273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86138803262635308613201697 64604102446976481459901273)
            ·
              refine ⟨48453076835232361094925955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64604102446976481459901273 48453076835232361094925955)
              ·
                refine ⟨72679615252848541642388933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48453076835232361094925955 72679615252848541642388933)
                ·
                  refine ⟨13627427859909101557947925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 72679615252848541642388933 13627427859909101557947925)
                  ·
                    refine ⟨638785680933239135528809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13627427859909101557947925 638785680933239135528809)
                    ·
                      rfl

theorem cell23_3732092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 1, 4, 6].length) (baseStart_3732092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3732092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3732092 prefixEnd_3732092 := by exact prefixLift 3732092
  have htrace : WordTrace (prefixWord ++ tailWord_3732092) baseStart_3732092 baseEnd_3732092 := by
    simpa [prefixWord, tailWord_3732092, baseEnd_3732092] using wordTrace_append hprefix tailTrace_3732092
  have hstable : (prefixWord ++ tailWord_3732092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3732092).length < 2 ^ (prefixWord ++ tailWord_3732092).sum := by decide
  have hdescent : baseEnd_3732092 < baseStart_3732092 := by decide
  rcases family_descends (prefixWord ++ tailWord_3732092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3732152 : List Nat := [2, 1, 2, 1, 2, 1, 1, 1, 5, 7]
def baseStart_3732152 : Nat := 118140960795 + 3732152 * 2 ^ 59
def prefixEnd_3732152 : Nat := 4983230072969 + 3 ^ 40 * 3732152 * 2
def baseEnd_3732152 : Nat := 638795950546329057278717

theorem tailTrace_3732152 : CollatzResearch.WordTrace tailWord_3732152 prefixEnd_3732152 638795950546329057278717 := by
  unfold tailWord_3732152
  simp only [CollatzResearch.WordTrace]
  refine ⟨68061383187529089830319355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90748510916705453107092473 68061383187529089830319355)
  ·
    refine ⟨102092074781293634745479033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68061383187529089830319355 102092074781293634745479033)
    ·
      refine ⟨76569056085970226059109275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102092074781293634745479033 76569056085970226059109275)
      ·
        refine ⟨114853584128955339088663913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76569056085970226059109275 114853584128955339088663913)
        ·
          refine ⟨86140188096716504316497935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114853584128955339088663913 86140188096716504316497935)
          ·
            refine ⟨129210282145074756474746903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86140188096716504316497935 129210282145074756474746903)
            ·
              refine ⟨193815423217612134712120355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 129210282145074756474746903 193815423217612134712120355)
              ·
                refine ⟨290723134826418202068180533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 193815423217612134712120355 290723134826418202068180533)
                ·
                  refine ⟨27255293889976706443891925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 290723134826418202068180533 27255293889976706443891925)
                  ·
                    refine ⟨638795950546329057278717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 27255293889976706443891925 638795950546329057278717)
                    ·
                      rfl

theorem cell23_3732152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 1, 5, 7].length) (baseStart_3732152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3732152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3732152 prefixEnd_3732152 := by exact prefixLift 3732152
  have htrace : WordTrace (prefixWord ++ tailWord_3732152) baseStart_3732152 baseEnd_3732152 := by
    simpa [prefixWord, tailWord_3732152, baseEnd_3732152] using wordTrace_append hprefix tailTrace_3732152
  have hstable : (prefixWord ++ tailWord_3732152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3732152).length < 2 ^ (prefixWord ++ tailWord_3732152).sum := by decide
  have hdescent : baseEnd_3732152 < baseStart_3732152 := by decide
  rcases family_descends (prefixWord ++ tailWord_3732152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3732156 : List Nat := [2, 2, 2, 3, 1, 1, 3, 4, 5]
def baseStart_3732156 : Nat := 118140960795 + 3732156 * 2 ^ 59
def prefixEnd_3732156 : Nat := 4983230072969 + 3 ^ 40 * 3732156 * 2
def baseEnd_3732156 : Nat := 212932211729067239576237

theorem tailTrace_3732156 : CollatzResearch.WordTrace tailWord_3732156 prefixEnd_3732156 212932211729067239576237 := by
  unfold tailWord_3732156
  simp only [CollatzResearch.WordTrace]
  refine ⟨68061456133521844171892161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90748608178029125562522881 68061456133521844171892161)
  ·
    refine ⟨51046092100141383128919121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68061456133521844171892161 51046092100141383128919121)
    ·
      refine ⟨38284569075106037346689341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51046092100141383128919121 38284569075106037346689341)
      ·
        refine ⟨14356713403164764005008503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38284569075106037346689341 14356713403164764005008503)
        ·
          refine ⟨21535070104747146007512755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14356713403164764005008503 21535070104747146007512755)
          ·
            refine ⟨32302605157120719011269133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21535070104747146007512755 32302605157120719011269133)
            ·
              refine ⟨12113476933920269629225925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32302605157120719011269133 12113476933920269629225925)
              ·
                refine ⟨2271276925110050555479861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12113476933920269629225925 2271276925110050555479861)
                ·
                  refine ⟨212932211729067239576237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2271276925110050555479861 212932211729067239576237)
                  ·
                    rfl

theorem cell23_3732156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 3, 4, 5].length) (baseStart_3732156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3732156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3732156 prefixEnd_3732156 := by exact prefixLift 3732156
  have htrace : WordTrace (prefixWord ++ tailWord_3732156) baseStart_3732156 baseEnd_3732156 := by
    simpa [prefixWord, tailWord_3732156, baseEnd_3732156] using wordTrace_append hprefix tailTrace_3732156
  have hstable : (prefixWord ++ tailWord_3732156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3732156).length < 2 ^ (prefixWord ++ tailWord_3732156).sum := by decide
  have hdescent : baseEnd_3732156 < baseStart_3732156 := by decide
  rcases family_descends (prefixWord ++ tailWord_3732156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3732173 : List Nat := [1, 6, 2, 1, 2, 1, 1, 2, 7]
def baseStart_3732173 : Nat := 118140960795 + 3732173 * 2 ^ 59
def prefixEnd_3732173 : Nat := 4983230072969 + 3 ^ 40 * 3732173 * 2
def baseEnd_3732173 : Nat := 212933181636970176630395

theorem tailTrace_3732173 : CollatzResearch.WordTrace tailWord_3732173 prefixEnd_3732173 212933181636970176630395 := by
  unfold tailWord_3732173
  simp only [CollatzResearch.WordTrace]
  refine ⟨136123532307982100247153173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90749021538654733498102115 136123532307982100247153173)
  ·
    refine ⟨6380790576936660949085305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 136123532307982100247153173 6380790576936660949085305)
    ·
      refine ⟨4785592932702495711813979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6380790576936660949085305 4785592932702495711813979)
      ·
        refine ⟨7178389399053743567720969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4785592932702495711813979 7178389399053743567720969)
        ·
          refine ⟨5383792049290307675790727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7178389399053743567720969 5383792049290307675790727)
          ·
            refine ⟨8075688073935461513686091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5383792049290307675790727 8075688073935461513686091)
            ·
              refine ⟨12113532110903192270529137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8075688073935461513686091 12113532110903192270529137)
              ·
                refine ⟨9085149083177394202896853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12113532110903192270529137 9085149083177394202896853)
                ·
                  refine ⟨212933181636970176630395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9085149083177394202896853 212933181636970176630395)
                  ·
                    rfl

theorem cell23_3732173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 1, 2, 7].length) (baseStart_3732173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3732173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3732173 prefixEnd_3732173 := by exact prefixLift 3732173
  have htrace : WordTrace (prefixWord ++ tailWord_3732173) baseStart_3732173 baseEnd_3732173 := by
    simpa [prefixWord, tailWord_3732173, baseEnd_3732173] using wordTrace_append hprefix tailTrace_3732173
  have hstable : (prefixWord ++ tailWord_3732173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3732173).length < 2 ^ (prefixWord ++ tailWord_3732173).sum := by decide
  have hdescent : baseEnd_3732173 < baseStart_3732173 := by decide
  rcases family_descends (prefixWord ++ tailWord_3732173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3732216 : List Nat := [2, 1, 2, 1, 1, 2, 6, 1, 3, 4]
def baseStart_3732216 : Nat := 118140960795 + 3732216 * 2 ^ 59
def prefixEnd_3732216 : Nat := 4983230072969 + 3 ^ 40 * 3732216 * 2
def baseEnd_3732216 : Nat := 638806904800291640478619

theorem tailTrace_3732216 : CollatzResearch.WordTrace tailWord_3732216 prefixEnd_3732216 638806904800291640478619 := by
  unfold tailWord_3732216
  simp only [CollatzResearch.WordTrace]
  refine ⟨68062550323413159295484251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90750067097884212393979001 68062550323413159295484251)
  ·
    refine ⟨102093825485119738943226377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68062550323413159295484251 102093825485119738943226377)
    ·
      refine ⟨76570369113839804207419783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102093825485119738943226377 76570369113839804207419783)
      ·
        refine ⟨114855553670759706311129675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76570369113839804207419783 114855553670759706311129675)
        ·
          refine ⟨172283330506139559466694513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114855553670759706311129675 172283330506139559466694513)
          ·
            refine ⟨129212497879604669600020885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 172283330506139559466694513 129212497879604669600020885)
            ·
              refine ⟨6056835838106468887500979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 129212497879604669600020885 6056835838106468887500979)
              ·
                refine ⟨9085253757159703331251469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6056835838106468887500979 9085253757159703331251469)
                ·
                  refine ⟨3406970158934888749219301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9085253757159703331251469 3406970158934888749219301)
                  ·
                    refine ⟨638806904800291640478619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3406970158934888749219301 638806904800291640478619)
                    ·
                      rfl

theorem cell23_3732216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 6, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 6, 1, 3, 4].length) (baseStart_3732216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3732216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3732216 prefixEnd_3732216 := by exact prefixLift 3732216
  have htrace : WordTrace (prefixWord ++ tailWord_3732216) baseStart_3732216 baseEnd_3732216 := by
    simpa [prefixWord, tailWord_3732216, baseEnd_3732216] using wordTrace_append hprefix tailTrace_3732216
  have hstable : (prefixWord ++ tailWord_3732216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3732216).length < 2 ^ (prefixWord ++ tailWord_3732216).sum := by decide
  have hdescent : baseEnd_3732216 < baseStart_3732216 := by decide
  rcases family_descends (prefixWord ++ tailWord_3732216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3732229 : List Nat := [1, 3, 1, 1, 2, 1, 1, 7, 6]
def baseStart_3732229 : Nat := 118140960795 + 3732229 * 2 ^ 59
def prefixEnd_3732229 : Nat := 4983230072969 + 3 ^ 40 * 3732229 * 2
def baseEnd_3732229 : Nat := 212936376627709263397033

theorem tailTrace_3732229 : CollatzResearch.WordTrace tailWord_3732229 prefixEnd_3732229 212936376627709263397033 := by
  unfold tailWord_3732229
  simp only [CollatzResearch.WordTrace]
  refine ⟨136125574795779221811191741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90750383197186147874127827 136125574795779221811191741)
  ·
    refine ⟨51047090548417208179196903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 136125574795779221811191741 51047090548417208179196903)
    ·
      refine ⟨76570635822625812268795355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51047090548417208179196903 76570635822625812268795355)
      ·
        refine ⟨114855953733938718403193033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76570635822625812268795355 114855953733938718403193033)
        ·
          refine ⟨86141965300454038802394775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114855953733938718403193033 86141965300454038802394775)
          ·
            refine ⟨129212947950681058203592163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86141965300454038802394775 129212947950681058203592163)
            ·
              refine ⟨193819421926021587305388245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 129212947950681058203592163 193819421926021587305388245)
              ·
                refine ⟨4542642701391130952470037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 193819421926021587305388245 4542642701391130952470037)
                ·
                  refine ⟨212936376627709263397033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4542642701391130952470037 212936376627709263397033)
                  ·
                    rfl

theorem cell23_3732229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 7, 6].length) (baseStart_3732229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3732229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3732229 prefixEnd_3732229 := by exact prefixLift 3732229
  have htrace : WordTrace (prefixWord ++ tailWord_3732229) baseStart_3732229 baseEnd_3732229 := by
    simpa [prefixWord, tailWord_3732229, baseEnd_3732229] using wordTrace_append hprefix tailTrace_3732229
  have hstable : (prefixWord ++ tailWord_3732229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3732229).length < 2 ^ (prefixWord ++ tailWord_3732229).sum := by decide
  have hdescent : baseEnd_3732229 < baseStart_3732229 := by decide
  rcases family_descends (prefixWord ++ tailWord_3732229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3732239 : List Nat := [1, 1, 2, 1, 1, 1, 5, 1, 2, 5, 3]
def baseStart_3732239 : Nat := 118140960795 + 3732239 * 2 ^ 59
def prefixEnd_3732239 : Nat := 4983230072969 + 3 ^ 40 * 3732239 * 2
def baseEnd_3732239 : Nat := 1916432524455928331448251

theorem tailTrace_3732239 : CollatzResearch.WordTrace tailWord_3732239 prefixEnd_3732239 1916432524455928331448251 := by
  unfold tailWord_3732239
  simp only [CollatzResearch.WordTrace]
  refine ⟨136125939525742993519055771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90750626350495329012703847 136125939525742993519055771)
  ·
    refine ⟨204188909288614490278583657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136125939525742993519055771 204188909288614490278583657)
    ·
      refine ⟨153141681966460867708937743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 204188909288614490278583657 153141681966460867708937743)
      ·
        refine ⟨229712522949691301563406615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153141681966460867708937743 229712522949691301563406615)
        ·
          refine ⟨344568784424536952345109923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 229712522949691301563406615 344568784424536952345109923)
          ·
            refine ⟨516853176636805428517664885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 344568784424536952345109923 516853176636805428517664885)
            ·
              refine ⟨48454985309700508923531083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 516853176636805428517664885 48454985309700508923531083)
              ·
                refine ⟨72682477964550763385296625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48454985309700508923531083 72682477964550763385296625)
                ·
                  refine ⟨54511858473413072538972469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 72682477964550763385296625 54511858473413072538972469)
                  ·
                    refine ⟨5110486731882475550528669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 54511858473413072538972469 5110486731882475550528669)
                    ·
                      refine ⟨1916432524455928331448251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5110486731882475550528669 1916432524455928331448251)
                      ·
                        rfl

theorem cell23_3732239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 1, 2, 5, 3].length) (baseStart_3732239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3732239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3732239 prefixEnd_3732239 := by exact prefixLift 3732239
  have htrace : WordTrace (prefixWord ++ tailWord_3732239) baseStart_3732239 baseEnd_3732239 := by
    simpa [prefixWord, tailWord_3732239, baseEnd_3732239] using wordTrace_append hprefix tailTrace_3732239
  have hstable : (prefixWord ++ tailWord_3732239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3732239).length < 2 ^ (prefixWord ++ tailWord_3732239).sum := by decide
  have hdescent : baseEnd_3732239 < baseStart_3732239 := by decide
  rcases family_descends (prefixWord ++ tailWord_3732239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3732259 : List Nat := [1, 1, 1, 4, 2, 1, 1, 2, 5, 5]
def baseStart_3732259 : Nat := 118140960795 + 3732259 * 2 ^ 59
def prefixEnd_3732259 : Nat := 4983230072969 + 3 ^ 40 * 3732259 * 2
def baseEnd_3732259 : Nat := 638814264689672751066053

theorem tailTrace_3732259 : CollatzResearch.WordTrace tailWord_3732259 prefixEnd_3732259 638814264689672751066053 := by
  unfold tailWord_3732259
  simp only [CollatzResearch.WordTrace]
  refine ⟨136126668985670536934783831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90751112657113691289855887 136126668985670536934783831)
  ·
    refine ⟨204190003478505805402175747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136126668985670536934783831 204190003478505805402175747)
    ·
      refine ⟨306285005217758708103263621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204190003478505805402175747 306285005217758708103263621)
      ·
        refine ⟨57428438478329757769361929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 306285005217758708103263621 57428438478329757769361929)
        ·
          refine ⟨43071328858747318327021447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57428438478329757769361929 43071328858747318327021447)
          ·
            refine ⟨64606993288120977490532171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43071328858747318327021447 64606993288120977490532171)
            ·
              refine ⟨96910489932181466235798257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64606993288120977490532171 96910489932181466235798257)
              ·
                refine ⟨72682867449136099676848693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 96910489932181466235798257 72682867449136099676848693)
                ·
                  refine ⟨6814018823356509344704565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 72682867449136099676848693 6814018823356509344704565)
                  ·
                    refine ⟨638814264689672751066053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6814018823356509344704565 638814264689672751066053)
                    ·
                      rfl

theorem cell23_3732259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 2, 5, 5].length) (baseStart_3732259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3732259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3732259 prefixEnd_3732259 := by exact prefixLift 3732259
  have htrace : WordTrace (prefixWord ++ tailWord_3732259) baseStart_3732259 baseEnd_3732259 := by
    simpa [prefixWord, tailWord_3732259, baseEnd_3732259] using wordTrace_append hprefix tailTrace_3732259
  have hstable : (prefixWord ++ tailWord_3732259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3732259).length < 2 ^ (prefixWord ++ tailWord_3732259).sum := by decide
  have hdescent : baseEnd_3732259 < baseStart_3732259 := by decide
  rcases family_descends (prefixWord ++ tailWord_3732259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3732296 : List Nat := [2, 1, 3, 1, 1, 3, 3, 1, 3, 1, 4]
def baseStart_3732296 : Nat := 118140960795 + 3732296 * 2 ^ 59
def prefixEnd_3732296 : Nat := 4983230072969 + 3 ^ 40 * 3732296 * 2
def baseEnd_3732296 : Nat := 1916461792853234608435489

theorem tailTrace_3732296 : CollatzResearch.WordTrace tailWord_3732296 prefixEnd_3732296 1916461792853234608435489 := by
  unfold tailWord_3732296
  simp only [CollatzResearch.WordTrace]
  refine ⟨68064009243268246126940371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90752012324357661502587161 68064009243268246126940371)
  ·
    refine ⟨102096013864902369190410557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68064009243268246126940371 102096013864902369190410557)
    ·
      refine ⟨38286005199338388446403959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102096013864902369190410557 38286005199338388446403959)
      ·
        refine ⟨57429007799007582669605939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38286005199338388446403959 57429007799007582669605939)
        ·
          refine ⟨86143511698511374004408909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57429007799007582669605939 86143511698511374004408909)
          ·
            refine ⟨32303816886941765251653341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 86143511698511374004408909 32303816886941765251653341)
            ·
              refine ⟨12113931332603161969370003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32303816886941765251653341 12113931332603161969370003)
              ·
                refine ⟨18170896998904742954055005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12113931332603161969370003 18170896998904742954055005)
                ·
                  refine ⟨6814086374589278607770627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18170896998904742954055005 6814086374589278607770627)
                  ·
                    refine ⟨10221129561883917911655941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6814086374589278607770627 10221129561883917911655941)
                    ·
                      refine ⟨1916461792853234608435489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10221129561883917911655941 1916461792853234608435489)
                      ·
                        rfl

theorem cell23_3732296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 3, 1, 3, 1, 4].length) (baseStart_3732296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3732296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3732296 prefixEnd_3732296 := by exact prefixLift 3732296
  have htrace : WordTrace (prefixWord ++ tailWord_3732296) baseStart_3732296 baseEnd_3732296 := by
    simpa [prefixWord, tailWord_3732296, baseEnd_3732296] using wordTrace_append hprefix tailTrace_3732296
  have hstable : (prefixWord ++ tailWord_3732296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3732296).length < 2 ^ (prefixWord ++ tailWord_3732296).sum := by decide
  have hdescent : baseEnd_3732296 < baseStart_3732296 := by decide
  rcases family_descends (prefixWord ++ tailWord_3732296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3732300 : List Nat := [2, 2, 1, 3, 3, 2, 2, 1, 2, 3, 2]
def baseStart_3732300 : Nat := 118140960795 + 3732300 * 2 ^ 59
def prefixEnd_3732300 : Nat := 4983230072969 + 3 ^ 40 * 3732300 * 2
def baseEnd_3732300 : Nat := 1916463846775852592785471

theorem tailTrace_3732300 : CollatzResearch.WordTrace tailWord_3732300 prefixEnd_3732300 1916463846775852592785471 := by
  unfold tailWord_3732300
  simp only [CollatzResearch.WordTrace]
  refine ⟨68064082189261000468513177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90752109585681333958017569 68064082189261000468513177)
  ·
    refine ⟨51048061641945750351384883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68064082189261000468513177 51048061641945750351384883)
    ·
      refine ⟨76572092462918625527077325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51048061641945750351384883 76572092462918625527077325)
      ·
        refine ⟨28714534673594484572653997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76572092462918625527077325 28714534673594484572653997)
        ·
          refine ⟨10767950502597931714745249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28714534673594484572653997 10767950502597931714745249)
          ·
            refine ⟨8075962876948448786058937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10767950502597931714745249 8075962876948448786058937)
            ·
              refine ⟨6056972157711336589544203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8075962876948448786058937 6056972157711336589544203)
              ·
                refine ⟨9085458236567004884316305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6056972157711336589544203 9085458236567004884316305)
                ·
                  refine ⟨6814093677425253663237229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9085458236567004884316305 6814093677425253663237229)
                  ·
                    refine ⟨2555285129034470123713961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6814093677425253663237229 2555285129034470123713961)
                    ·
                      refine ⟨1916463846775852592785471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2555285129034470123713961 1916463846775852592785471)
                      ·
                        rfl

theorem cell23_3732300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 2, 1, 2, 3, 2].length) (baseStart_3732300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3732300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3732300 prefixEnd_3732300 := by exact prefixLift 3732300
  have htrace : WordTrace (prefixWord ++ tailWord_3732300) baseStart_3732300 baseEnd_3732300 := by
    simpa [prefixWord, tailWord_3732300, baseEnd_3732300] using wordTrace_append hprefix tailTrace_3732300
  have hstable : (prefixWord ++ tailWord_3732300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3732300).length < 2 ^ (prefixWord ++ tailWord_3732300).sum := by decide
  have hdescent : baseEnd_3732300 < baseStart_3732300 := by decide
  rcases family_descends (prefixWord ++ tailWord_3732300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3732306 : List Nat := [3, 2, 2, 1, 1, 2, 3, 2, 1, 6]
def baseStart_3732306 : Nat := 118140960795 + 3732306 * 2 ^ 59
def prefixEnd_3732306 : Nat := 4983230072969 + 3 ^ 40 * 3732306 * 2
def baseEnd_3732306 : Nat := 638822309219926523103481

theorem tailTrace_3732306 : CollatzResearch.WordTrace tailWord_3732306 prefixEnd_3732306 638822309219926523103481 := by
  unfold tailWord_3732306
  simp only [CollatzResearch.WordTrace]
  refine ⟨34032095804125065990436193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90752255477666842641163181 34032095804125065990436193)
  ·
    refine ⟨25524071853093799492827145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34032095804125065990436193 25524071853093799492827145)
    ·
      refine ⟨19143053889820349619620359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25524071853093799492827145 19143053889820349619620359)
      ·
        refine ⟨28714580834730524429430539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19143053889820349619620359 28714580834730524429430539)
        ·
          refine ⟨43071871252095786644145809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28714580834730524429430539 43071871252095786644145809)
          ·
            refine ⟨32303903439071839983109357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43071871252095786644145809 32303903439071839983109357)
            ·
              refine ⟨12113963789651939993666009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32303903439071839983109357 12113963789651939993666009)
              ·
                refine ⟨9085472842238954995249507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12113963789651939993666009 9085472842238954995249507)
                ·
                  refine ⟨13628209263358432492874261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9085472842238954995249507 13628209263358432492874261)
                  ·
                    refine ⟨638822309219926523103481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13628209263358432492874261 638822309219926523103481)
                    ·
                      rfl

theorem cell23_3732306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 3, 2, 1, 6].length) (baseStart_3732306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3732306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3732306 prefixEnd_3732306 := by exact prefixLift 3732306
  have htrace : WordTrace (prefixWord ++ tailWord_3732306) baseStart_3732306 baseEnd_3732306 := by
    simpa [prefixWord, tailWord_3732306, baseEnd_3732306] using wordTrace_append hprefix tailTrace_3732306
  have hstable : (prefixWord ++ tailWord_3732306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3732306).length < 2 ^ (prefixWord ++ tailWord_3732306).sum := by decide
  have hdescent : baseEnd_3732306 < baseStart_3732306 := by decide
  rcases family_descends (prefixWord ++ tailWord_3732306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3732323 : List Nat := [1, 1, 1, 5, 3, 1, 1, 4, 2, 4]
def baseStart_3732323 : Nat := 118140960795 + 3732323 * 2 ^ 59
def prefixEnd_3732323 : Nat := 4983230072969 + 3 ^ 40 * 3732323 * 2
def baseEnd_3732323 : Nat := 638825218943635334265955

theorem tailTrace_3732323 : CollatzResearch.WordTrace tailWord_3732323 prefixEnd_3732323 638825218943635334265955 := by
  unfold tailWord_3732323
  simp only [CollatzResearch.WordTrace]
  refine ⟨136129003257438675865113623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90752668838292450576742415 136129003257438675865113623)
  ·
    refine ⟨204193504886158013797670435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136129003257438675865113623 204193504886158013797670435)
    ·
      refine ⟨306290257329237020696505653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204193504886158013797670435 306290257329237020696505653)
      ·
        refine ⟨28714711624615970690297405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 306290257329237020696505653 28714711624615970690297405)
        ·
          refine ⟨10768016859230989008861527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28714711624615970690297405 10768016859230989008861527)
          ·
            refine ⟨16152025288846483513292291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10768016859230989008861527 16152025288846483513292291)
            ·
              refine ⟨24228037933269725269938437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16152025288846483513292291 24228037933269725269938437)
              ·
                refine ⟨4542757112488073488113457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24228037933269725269938437 4542757112488073488113457)
                ·
                  refine ⟨3407067834366055116085093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4542757112488073488113457 3407067834366055116085093)
                  ·
                    refine ⟨638825218943635334265955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3407067834366055116085093 638825218943635334265955)
                    ·
                      rfl

theorem cell23_3732323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 1, 4, 2, 4].length) (baseStart_3732323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3732323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3732323 prefixEnd_3732323 := by exact prefixLift 3732323
  have htrace : WordTrace (prefixWord ++ tailWord_3732323) baseStart_3732323 baseEnd_3732323 := by
    simpa [prefixWord, tailWord_3732323, baseEnd_3732323] using wordTrace_append hprefix tailTrace_3732323
  have hstable : (prefixWord ++ tailWord_3732323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3732323).length < 2 ^ (prefixWord ++ tailWord_3732323).sum := by decide
  have hdescent : baseEnd_3732323 < baseStart_3732323 := by decide
  rcases family_descends (prefixWord ++ tailWord_3732323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3732324 : List Nat := [2, 3, 1, 1, 4, 3, 2, 2, 1, 1, 3]
def baseStart_3732324 : Nat := 118140960795 + 3732324 * 2 ^ 59
def prefixEnd_3732324 : Nat := 4983230072969 + 3 ^ 40 * 3732324 * 2
def baseEnd_3732324 : Nat := 1916476170311560498885361

theorem tailTrace_3732324 : CollatzResearch.WordTrace tailWord_3732324 prefixEnd_3732324 1916476170311560498885361 := by
  unfold tailWord_3732324
  simp only [CollatzResearch.WordTrace]
  refine ⟨68064519865217526517950013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90752693153623368690600017 68064519865217526517950013)
  ·
    refine ⟨25524194949456572444231255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68064519865217526517950013 25524194949456572444231255)
    ·
      refine ⟨38286292424184858666346883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25524194949456572444231255 38286292424184858666346883)
      ·
        refine ⟨57429438636277287999520325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38286292424184858666346883 57429438636277287999520325)
        ·
          refine ⟨10768019744301991499910061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 57429438636277287999520325 10768019744301991499910061)
          ·
            refine ⟨4038007404113246812466273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10768019744301991499910061 4038007404113246812466273)
            ·
              refine ⟨3028505553084935109349705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4038007404113246812466273 3028505553084935109349705)
              ·
                refine ⟨2271379164813701332012279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3028505553084935109349705 2271379164813701332012279)
                ·
                  refine ⟨3407068747220551998018419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2271379164813701332012279 3407068747220551998018419)
                  ·
                    refine ⟨5110603120830827997027629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3407068747220551998018419 5110603120830827997027629)
                    ·
                      refine ⟨1916476170311560498885361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5110603120830827997027629 1916476170311560498885361)
                      ·
                        rfl

theorem cell23_3732324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 3, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 3, 2, 2, 1, 1, 3].length) (baseStart_3732324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3732324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3732324 prefixEnd_3732324 := by exact prefixLift 3732324
  have htrace : WordTrace (prefixWord ++ tailWord_3732324) baseStart_3732324 baseEnd_3732324 := by
    simpa [prefixWord, tailWord_3732324, baseEnd_3732324] using wordTrace_append hprefix tailTrace_3732324
  have hstable : (prefixWord ++ tailWord_3732324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3732324).length < 2 ^ (prefixWord ++ tailWord_3732324).sum := by decide
  have hdescent : baseEnd_3732324 < baseStart_3732324 := by decide
  rcases family_descends (prefixWord ++ tailWord_3732324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3732339 : List Nat := [1, 1, 1, 2, 2, 1, 4, 1, 2, 2, 6]
def baseStart_3732339 : Nat := 118140960795 + 3732339 * 2 ^ 59
def prefixEnd_3732339 : Nat := 4983230072969 + 3 ^ 40 * 3732339 * 2
def baseEnd_3732339 : Nat := 1916483872521377940197791

theorem tailTrace_3732339 : CollatzResearch.WordTrace tailWord_3732339 prefixEnd_3732339 1916483872521377940197791 := by
  unfold tailWord_3732339
  simp only [CollatzResearch.WordTrace]
  refine ⟨136129586825380710597696071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90753057883587140398464047 136129586825380710597696071)
  ·
    refine ⟨204194380238071065896544107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136129586825380710597696071 204194380238071065896544107)
    ·
      refine ⟨306291570357106598844816161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204194380238071065896544107 306291570357106598844816161)
      ·
        refine ⟨229718677767829949133612121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 306291570357106598844816161 229718677767829949133612121)
        ·
          refine ⟨172289008325872461850209091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 229718677767829949133612121 172289008325872461850209091)
          ·
            refine ⟨258433512488808692775313637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 172289008325872461850209091 258433512488808692775313637)
            ·
              refine ⟨48456283591651629895371307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 258433512488808692775313637 48456283591651629895371307)
              ·
                refine ⟨72684425387477444843056961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48456283591651629895371307 72684425387477444843056961)
                ·
                  refine ⟨54513319040608083632292721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 72684425387477444843056961 54513319040608083632292721)
                  ·
                    refine ⟨40884989280456062724219541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 54513319040608083632292721 40884989280456062724219541)
                    ·
                      refine ⟨1916483872521377940197791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 40884989280456062724219541 1916483872521377940197791)
                      ·
                        rfl

theorem cell23_3732339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 1, 2, 2, 6].length) (baseStart_3732339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3732339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3732339 prefixEnd_3732339 := by exact prefixLift 3732339
  have htrace : WordTrace (prefixWord ++ tailWord_3732339) baseStart_3732339 baseEnd_3732339 := by
    simpa [prefixWord, tailWord_3732339, baseEnd_3732339] using wordTrace_append hprefix tailTrace_3732339
  have hstable : (prefixWord ++ tailWord_3732339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3732339).length < 2 ^ (prefixWord ++ tailWord_3732339).sum := by decide
  have hdescent : baseEnd_3732339 < baseStart_3732339 := by decide
  rcases family_descends (prefixWord ++ tailWord_3732339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3732374 : List Nat := [5, 3, 1, 1, 1, 1, 3, 2, 2, 4]
def baseStart_3732374 : Nat := 118140960795 + 3732374 * 2 ^ 59
def prefixEnd_3732374 : Nat := 4983230072969 + 3 ^ 40 * 3732374 * 2
def baseEnd_3732374 : Nat := 638833948114761767753377

theorem tailTrace_3732374 : CollatzResearch.WordTrace tailWord_3732374 prefixEnd_3732374 638833948114761767753377 := by
  unfold tailWord_3732374
  simp only [CollatzResearch.WordTrace]
  refine ⟨8508178961265869473451261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 90753908920169274383480117 8508178961265869473451261)
  ·
    refine ⟨3190567110474701052544223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8508178961265869473451261 3190567110474701052544223)
    ·
      refine ⟨4785850665712051578816335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3190567110474701052544223 4785850665712051578816335)
      ·
        refine ⟨7178775998568077368224503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4785850665712051578816335 7178775998568077368224503)
        ·
          refine ⟨10768163997852116052336755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7178775998568077368224503 10768163997852116052336755)
          ·
            refine ⟨16152245996778174078505133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10768163997852116052336755 16152245996778174078505133)
            ·
              refine ⟨6057092248791815279439425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16152245996778174078505133 6057092248791815279439425)
              ·
                refine ⟨4542819186593861459579569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6057092248791815279439425 4542819186593861459579569)
                ·
                  refine ⟨3407114389945396094684677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4542819186593861459579569 3407114389945396094684677)
                  ·
                    refine ⟨638833948114761767753377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3407114389945396094684677 638833948114761767753377)
                    ·
                      rfl

theorem cell23_3732374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 3, 2, 2, 4].length) (baseStart_3732374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3732374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3732374 prefixEnd_3732374 := by exact prefixLift 3732374
  have htrace : WordTrace (prefixWord ++ tailWord_3732374) baseStart_3732374 baseEnd_3732374 := by
    simpa [prefixWord, tailWord_3732374, baseEnd_3732374] using wordTrace_append hprefix tailTrace_3732374
  have hstable : (prefixWord ++ tailWord_3732374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3732374).length < 2 ^ (prefixWord ++ tailWord_3732374).sum := by decide
  have hdescent : baseEnd_3732374 < baseStart_3732374 := by decide
  rcases family_descends (prefixWord ++ tailWord_3732374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3732403 : List Nat := [1, 1, 1, 2, 3, 1, 2, 5, 1, 4, 2]
def baseStart_3732403 : Nat := 118140960795 + 3732403 * 2 ^ 59
def prefixEnd_3732403 : Nat := 4983230072969 + 3 ^ 40 * 3732403 * 2
def baseEnd_3732403 : Nat := 1916516735283265689797497

theorem tailTrace_3732403 : CollatzResearch.WordTrace tailWord_3732403 prefixEnd_3732403 1916516735283265689797497 := by
  unfold tailWord_3732403
  simp only [CollatzResearch.WordTrace]
  refine ⟨136131921097148849528025863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90754614064765899685350575 136131921097148849528025863)
  ·
    refine ⟨204197881645723274292038795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136131921097148849528025863 204197881645723274292038795)
    ·
      refine ⟨306296822468584911438058193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204197881645723274292038795 306296822468584911438058193)
      ·
        refine ⟨229722616851438683578543645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 306296822468584911438058193 229722616851438683578543645)
        ·
          refine ⟨86145981319289506341953867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 229722616851438683578543645 86145981319289506341953867)
          ·
            refine ⟨129218971978934259512930801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86145981319289506341953867 129218971978934259512930801)
            ·
              refine ⟨96914228984200694634698101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 129218971978934259512930801 96914228984200694634698101)
              ·
                refine ⟨9085708967268815122002947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 96914228984200694634698101 9085708967268815122002947)
                ·
                  refine ⟨13628563450903222683004421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9085708967268815122002947 13628563450903222683004421)
                  ·
                    refine ⟨2555355647044354253063329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13628563450903222683004421 2555355647044354253063329)
                    ·
                      refine ⟨1916516735283265689797497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2555355647044354253063329 1916516735283265689797497)
                      ·
                        rfl

theorem cell23_3732403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 5, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 5, 1, 4, 2].length) (baseStart_3732403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3732403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3732403 prefixEnd_3732403 := by exact prefixLift 3732403
  have htrace : WordTrace (prefixWord ++ tailWord_3732403) baseStart_3732403 baseEnd_3732403 := by
    simpa [prefixWord, tailWord_3732403, baseEnd_3732403] using wordTrace_append hprefix tailTrace_3732403
  have hstable : (prefixWord ++ tailWord_3732403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3732403).length < 2 ^ (prefixWord ++ tailWord_3732403).sum := by decide
  have hdescent : baseEnd_3732403 < baseStart_3732403 := by decide
  rcases family_descends (prefixWord ++ tailWord_3732403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3732456 : List Nat := [2, 1, 4, 1, 1, 1, 2, 1, 3, 7]
def baseStart_3732456 : Nat := 118140960795 + 3732456 * 2 ^ 59
def prefixEnd_3732456 : Nat := 4983230072969 + 3 ^ 40 * 3732456 * 2
def baseEnd_3732456 : Nat := 638847983252651327478251

theorem tailTrace_3732456 : CollatzResearch.WordTrace tailWord_3732456 prefixEnd_3732456 638847983252651327478251 := by
  unfold tailWord_3732456
  simp only [CollatzResearch.WordTrace]
  refine ⟨68066927082978419789852611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90755902777304559719803481 68066927082978419789852611)
  ·
    refine ⟨102100390624467629684778917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68066927082978419789852611 102100390624467629684778917)
    ·
      refine ⟨19143823242087680565896047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 102100390624467629684778917 19143823242087680565896047)
      ·
        refine ⟨28715734863131520848844071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19143823242087680565896047 28715734863131520848844071)
        ·
          refine ⟨43073602294697281273266107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28715734863131520848844071 43073602294697281273266107)
          ·
            refine ⟨64610403442045921909899161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43073602294697281273266107 64610403442045921909899161)
            ·
              refine ⟨48457802581534441432424371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64610403442045921909899161 48457802581534441432424371)
              ·
                refine ⟨72686703872301662148636557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48457802581534441432424371 72686703872301662148636557)
                ·
                  refine ⟨27257513952113123305738709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 72686703872301662148636557 27257513952113123305738709)
                  ·
                    refine ⟨638847983252651327478251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 27257513952113123305738709 638847983252651327478251)
                    ·
                      rfl

theorem cell23_3732456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 1, 3, 7].length) (baseStart_3732456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3732456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3732456 prefixEnd_3732456 := by exact prefixLift 3732456
  have htrace : WordTrace (prefixWord ++ tailWord_3732456) baseStart_3732456 baseEnd_3732456 := by
    simpa [prefixWord, tailWord_3732456, baseEnd_3732456] using wordTrace_append hprefix tailTrace_3732456
  have hstable : (prefixWord ++ tailWord_3732456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3732456).length < 2 ^ (prefixWord ++ tailWord_3732456).sum := by decide
  have hdescent : baseEnd_3732456 < baseStart_3732456 := by decide
  rcases family_descends (prefixWord ++ tailWord_3732456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3732473 : List Nat := [1, 2, 1, 3, 1, 3, 4, 1, 2, 5]
def baseStart_3732473 : Nat := 118140960795 + 3732473 * 2 ^ 59
def prefixEnd_3732473 : Nat := 4983230072969 + 3 ^ 40 * 3732473 * 2
def baseEnd_3732473 : Nat := 638850892976360138640725

theorem tailTrace_3732473 : CollatzResearch.WordTrace tailWord_3732473 prefixEnd_3732473 638850892976360138640725 := by
  unfold tailWord_3732473
  simp only [CollatzResearch.WordTrace]
  refine ⟨136134474206895251483074073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90756316137930167655382715 136134474206895251483074073)
  ·
    refine ⟨102100855655171438612305555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136134474206895251483074073 102100855655171438612305555)
    ·
      refine ⟨153151283482757157918458333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102100855655171438612305555 153151283482757157918458333)
      ·
        refine ⟨57431731306033934219421875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 153151283482757157918458333 57431731306033934219421875)
        ·
          refine ⟨86147596959050901329132813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57431731306033934219421875 86147596959050901329132813)
          ·
            refine ⟨32305348859644087998424805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 86147596959050901329132813 32305348859644087998424805)
            ·
              refine ⟨6057252911183266499704651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32305348859644087998424805 6057252911183266499704651)
              ·
                refine ⟨9085879366774899749556977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6057252911183266499704651 9085879366774899749556977)
                ·
                  refine ⟨6814409525081174812167733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9085879366774899749556977 6814409525081174812167733)
                  ·
                    refine ⟨638850892976360138640725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6814409525081174812167733 638850892976360138640725)
                    ·
                      rfl

theorem cell23_3732473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 4, 1, 2, 5].length) (baseStart_3732473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3732473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3732473 prefixEnd_3732473 := by exact prefixLift 3732473
  have htrace : WordTrace (prefixWord ++ tailWord_3732473) baseStart_3732473 baseEnd_3732473 := by
    simpa [prefixWord, tailWord_3732473, baseEnd_3732473] using wordTrace_append hprefix tailTrace_3732473
  have hstable : (prefixWord ++ tailWord_3732473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3732473).length < 2 ^ (prefixWord ++ tailWord_3732473).sum := by decide
  have hdescent : baseEnd_3732473 < baseStart_3732473 := by decide
  rcases family_descends (prefixWord ++ tailWord_3732473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3732537 : List Nat := [1, 2, 1, 5, 2, 1, 1, 5, 1, 4]
def baseStart_3732537 : Nat := 118140960795 + 3732537 * 2 ^ 59
def prefixEnd_3732537 : Nat := 4983230072969 + 3 ^ 40 * 3732537 * 2
def baseEnd_3732537 : Nat := 638861847230322721840627

theorem tailTrace_3732537 : CollatzResearch.WordTrace tailWord_3732537 prefixEnd_3732537 638861847230322721840627 := by
  unfold tailWord_3732537
  simp only [CollatzResearch.WordTrace]
  refine ⟨136136808478663390413403865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90757872319108926942269243 136136808478663390413403865)
  ·
    refine ⟨102102606358997542810052899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136136808478663390413403865 102102606358997542810052899)
    ·
      refine ⟨153153909538496314215079349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102102606358997542810052899 153153909538496314215079349)
      ·
        refine ⟨14358179019234029457663689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 153153909538496314215079349 14358179019234029457663689)
        ·
          refine ⟨10768634264425522093247767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14358179019234029457663689 10768634264425522093247767)
          ·
            refine ⟨16152951396638283139871651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10768634264425522093247767 16152951396638283139871651)
            ·
              refine ⟨24229427094957424709807477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16152951396638283139871651 24229427094957424709807477)
              ·
                refine ⟨2271508790152258566544451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24229427094957424709807477 2271508790152258566544451)
                ·
                  refine ⟨3407263185228387849816677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2271508790152258566544451 3407263185228387849816677)
                  ·
                    refine ⟨638861847230322721840627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3407263185228387849816677 638861847230322721840627)
                    ·
                      rfl

theorem cell23_3732537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 1, 5, 1, 4].length) (baseStart_3732537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3732537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3732537 prefixEnd_3732537 := by exact prefixLift 3732537
  have htrace : WordTrace (prefixWord ++ tailWord_3732537) baseStart_3732537 baseEnd_3732537 := by
    simpa [prefixWord, tailWord_3732537, baseEnd_3732537] using wordTrace_append hprefix tailTrace_3732537
  have hstable : (prefixWord ++ tailWord_3732537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3732537).length < 2 ^ (prefixWord ++ tailWord_3732537).sum := by decide
  have hdescent : baseEnd_3732537 < baseStart_3732537 := by decide
  rcases family_descends (prefixWord ++ tailWord_3732537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3732570 : List Nat := [3, 1, 1, 2, 1, 1, 2, 1, 6, 3, 2]
def baseStart_3732570 : Nat := 118140960795 + 3732570 * 2 ^ 59
def prefixEnd_3732570 : Nat := 4983230072969 + 3 ^ 40 * 3732570 * 2
def baseEnd_3732570 : Nat := 1916602486552566536409229

theorem tailTrace_3732570 : CollatzResearch.WordTrace tailWord_3732570 prefixEnd_3732570 1916602486552566536409229 := by
  unfold tailWord_3732570
  simp only [CollatzResearch.WordTrace]
  refine ⟨34034503021885959262338791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90758674725029224699570109 34034503021885959262338791)
  ·
    refine ⟨51051754532828938893508187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34034503021885959262338791 51051754532828938893508187)
    ·
      refine ⟨76577631799243408340262281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51051754532828938893508187 76577631799243408340262281)
      ·
        refine ⟨57433223849432556255196711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76577631799243408340262281 57433223849432556255196711)
        ·
          refine ⟨86149835774148834382795067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57433223849432556255196711 86149835774148834382795067)
          ·
            refine ⟨129224753661223251574192601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86149835774148834382795067 129224753661223251574192601)
            ·
              refine ⟨96918565245917438680644451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 129224753661223251574192601 96918565245917438680644451)
              ·
                refine ⟨145377847868876158020966677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 96918565245917438680644451 145377847868876158020966677)
                ·
                  refine ⟨6814586618853569907232813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 145377847868876158020966677 6814586618853569907232813)
                  ·
                    refine ⟨2555469982070088715212305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6814586618853569907232813 2555469982070088715212305)
                    ·
                      refine ⟨1916602486552566536409229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2555469982070088715212305 1916602486552566536409229)
                      ·
                        rfl

theorem cell23_3732570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 1, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 1, 6, 3, 2].length) (baseStart_3732570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3732570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3732570 prefixEnd_3732570 := by exact prefixLift 3732570
  have htrace : WordTrace (prefixWord ++ tailWord_3732570) baseStart_3732570 baseEnd_3732570 := by
    simpa [prefixWord, tailWord_3732570, baseEnd_3732570] using wordTrace_append hprefix tailTrace_3732570
  have hstable : (prefixWord ++ tailWord_3732570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3732570).length < 2 ^ (prefixWord ++ tailWord_3732570).sum := by decide
  have hdescent : baseEnd_3732570 < baseStart_3732570 := by decide
  rcases family_descends (prefixWord ++ tailWord_3732570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3732600 : List Nat := [2, 1, 2, 1, 1, 1, 6, 3, 1, 1, 4]
def baseStart_3732600 : Nat := 118140960795 + 3732600 * 2 ^ 59
def prefixEnd_3732600 : Nat := 4983230072969 + 3 ^ 40 * 3732600 * 2
def baseEnd_3732600 : Nat := 1916617890972201419034091

theorem tailTrace_3732600 : CollatzResearch.WordTrace tailWord_3732600 prefixEnd_3732600 1916617890972201419034091 := by
  unfold tailWord_3732600
  simp only [CollatzResearch.WordTrace]
  refine ⟨68069553138717576086473627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90759404184956768115298169 68069553138717576086473627)
  ·
    refine ⟨102104329708076364129710441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68069553138717576086473627 102104329708076364129710441)
    ·
      refine ⟨76578247281057273097282831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102104329708076364129710441 76578247281057273097282831)
      ·
        refine ⟨114867370921585909645924247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76578247281057273097282831 114867370921585909645924247)
        ·
          refine ⟨172301056382378864468886371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114867370921585909645924247 172301056382378864468886371)
          ·
            refine ⟨258451584573568296703329557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 172301056382378864468886371 258451584573568296703329557)
            ·
              refine ⟨12114918026886013907968573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 258451584573568296703329557 12114918026886013907968573)
              ·
                refine ⟨4543094260082255215488215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12114918026886013907968573 4543094260082255215488215)
                ·
                  refine ⟨6814641390123382823232323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4543094260082255215488215 6814641390123382823232323)
                  ·
                    refine ⟨10221962085185074234848485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6814641390123382823232323 10221962085185074234848485)
                    ·
                      refine ⟨1916617890972201419034091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10221962085185074234848485 1916617890972201419034091)
                      ·
                        rfl

theorem cell23_3732600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 6, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 6, 3, 1, 1, 4].length) (baseStart_3732600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3732600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3732600 prefixEnd_3732600 := by exact prefixLift 3732600
  have htrace : WordTrace (prefixWord ++ tailWord_3732600) baseStart_3732600 baseEnd_3732600 := by
    simpa [prefixWord, tailWord_3732600, baseEnd_3732600] using wordTrace_append hprefix tailTrace_3732600
  have hstable : (prefixWord ++ tailWord_3732600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3732600).length < 2 ^ (prefixWord ++ tailWord_3732600).sum := by decide
  have hdescent : baseEnd_3732600 < baseStart_3732600 := by decide
  rcases family_descends (prefixWord ++ tailWord_3732600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3732627 : List Nat := [1, 1, 1, 2, 1, 2, 8, 1, 2, 4]
def baseStart_3732627 : Nat := 118140960795 + 3732627 * 2 ^ 59
def prefixEnd_3732627 : Nat := 4983230072969 + 3 ^ 40 * 3732627 * 2
def baseEnd_3732627 : Nat := 638877251649957604465489

theorem tailTrace_3732627 : CollatzResearch.WordTrace tailWord_3732627 prefixEnd_3732627 638877251649957604465489 := by
  unfold tailWord_3732627
  simp only [CollatzResearch.WordTrace]
  refine ⟨136140091048337335784180135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90760060698891557189453423 136140091048337335784180135)
  ·
    refine ⟨204210136572506003676270203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136140091048337335784180135 204210136572506003676270203)
    ·
      refine ⟨306315204858759005514405305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204210136572506003676270203 306315204858759005514405305)
      ·
        refine ⟨229736403644069254135803979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 306315204858759005514405305 229736403644069254135803979)
        ·
          refine ⟨344604605466103881203705969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 229736403644069254135803979 344604605466103881203705969)
          ·
            refine ⟨258453454099577910902779477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 344604605466103881203705969 258453454099577910902779477)
            ·
              refine ⟨3028751415229428643391947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 258453454099577910902779477 3028751415229428643391947)
              ·
                refine ⟨4543127122844142965087921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3028751415229428643391947 4543127122844142965087921)
                ·
                  refine ⟨3407345342133107223815941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4543127122844142965087921 3407345342133107223815941)
                  ·
                    refine ⟨638877251649957604465489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3407345342133107223815941 638877251649957604465489)
                    ·
                      rfl

theorem cell23_3732627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 8, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 8, 1, 2, 4].length) (baseStart_3732627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3732627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3732627 prefixEnd_3732627 := by exact prefixLift 3732627
  have htrace : WordTrace (prefixWord ++ tailWord_3732627) baseStart_3732627 baseEnd_3732627 := by
    simpa [prefixWord, tailWord_3732627, baseEnd_3732627] using wordTrace_append hprefix tailTrace_3732627
  have hstable : (prefixWord ++ tailWord_3732627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3732627).length < 2 ^ (prefixWord ++ tailWord_3732627).sum := by decide
  have hdescent : baseEnd_3732627 < baseStart_3732627 := by decide
  rcases family_descends (prefixWord ++ tailWord_3732627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3732634 : List Nat := [3, 1, 1, 5, 1, 3, 1, 2, 1, 1, 4]
def baseStart_3732634 : Nat := 118140960795 + 3732634 * 2 ^ 59
def prefixEnd_3732634 : Nat := 4983230072969 + 3 ^ 40 * 3732634 * 2
def baseEnd_3732634 : Nat := 1916635349314454286008935

theorem tailTrace_3732634 : CollatzResearch.WordTrace tailWord_3732634 prefixEnd_3732634 1916635349314454286008935 := by
  unfold tailWord_3732634
  simp only [CollatzResearch.WordTrace]
  refine ⟨34035086589827993994921239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90760230906207983986456637 34035086589827993994921239)
  ·
    refine ⟨51052629884741990992381859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34035086589827993994921239 51052629884741990992381859)
    ·
      refine ⟨76578944827112986488572789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51052629884741990992381859 76578944827112986488572789)
      ·
        refine ⟨7179276077541842483303699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 76578944827112986488572789 7179276077541842483303699)
        ·
          refine ⟨10768914116312763724955549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7179276077541842483303699 10768914116312763724955549)
          ·
            refine ⟨4038342793617286396858331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10768914116312763724955549 4038342793617286396858331)
            ·
              refine ⟨6057514190425929595287497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4038342793617286396858331 6057514190425929595287497)
              ·
                refine ⟨4543135642819447196465623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6057514190425929595287497 4543135642819447196465623)
                ·
                  refine ⟨6814703464229170794698435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4543135642819447196465623 6814703464229170794698435)
                  ·
                    refine ⟨10222055196343756192047653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6814703464229170794698435 10222055196343756192047653)
                    ·
                      refine ⟨1916635349314454286008935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10222055196343756192047653 1916635349314454286008935)
                      ·
                        rfl

theorem cell23_3732634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 3, 1, 2, 1, 1, 4].length) (baseStart_3732634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3732634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3732634 prefixEnd_3732634 := by exact prefixLift 3732634
  have htrace : WordTrace (prefixWord ++ tailWord_3732634) baseStart_3732634 baseEnd_3732634 := by
    simpa [prefixWord, tailWord_3732634, baseEnd_3732634] using wordTrace_append hprefix tailTrace_3732634
  have hstable : (prefixWord ++ tailWord_3732634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3732634).length < 2 ^ (prefixWord ++ tailWord_3732634).sum := by decide
  have hdescent : baseEnd_3732634 < baseStart_3732634 := by decide
  rcases family_descends (prefixWord ++ tailWord_3732634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3732647 : List Nat := [1, 1, 6, 2, 1, 2, 1, 2, 1, 2, 4]
def baseStart_3732647 : Nat := 118140960795 + 3732647 * 2 ^ 59
def prefixEnd_3732647 : Nat := 4983230072969 + 3 ^ 40 * 3732647 * 2
def baseEnd_3732647 : Nat := 1916642024562962735146375

theorem tailTrace_3732647 : CollatzResearch.WordTrace tailWord_3732647 prefixEnd_3732647 1916642024562962735146375 := by
  unfold tailWord_3732647
  simp only [CollatzResearch.WordTrace]
  refine ⟨136140820508264879199908195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90760547005509919466605463 136140820508264879199908195)
  ·
    refine ⟨204211230762397318799862293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136140820508264879199908195 204211230762397318799862293)
    ·
      refine ⟨9572401441987374318743545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 204211230762397318799862293 9572401441987374318743545)
      ·
        refine ⟨7179301081490530739057659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9572401441987374318743545 7179301081490530739057659)
        ·
          refine ⟨10768951622235796108586489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7179301081490530739057659 10768951622235796108586489)
          ·
            refine ⟨8076713716676847081439867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10768951622235796108586489 8076713716676847081439867)
            ·
              refine ⟨12115070575015270622159801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8076713716676847081439867 12115070575015270622159801)
              ·
                refine ⟨9086302931261452966619851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12115070575015270622159801 9086302931261452966619851)
                ·
                  refine ⟨13629454396892179449929777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9086302931261452966619851 13629454396892179449929777)
                  ·
                    refine ⟨10222090797669134587447333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13629454396892179449929777 10222090797669134587447333)
                    ·
                      refine ⟨1916642024562962735146375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10222090797669134587447333 1916642024562962735146375)
                      ·
                        rfl

theorem cell23_3732647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 1, 2, 1, 2, 4].length) (baseStart_3732647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3732647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3732647 prefixEnd_3732647 := by exact prefixLift 3732647
  have htrace : WordTrace (prefixWord ++ tailWord_3732647) baseStart_3732647 baseEnd_3732647 := by
    simpa [prefixWord, tailWord_3732647, baseEnd_3732647] using wordTrace_append hprefix tailTrace_3732647
  have hstable : (prefixWord ++ tailWord_3732647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3732647).length < 2 ^ (prefixWord ++ tailWord_3732647).sum := by decide
  have hdescent : baseEnd_3732647 < baseStart_3732647 := by decide
  rcases family_descends (prefixWord ++ tailWord_3732647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3732662 : List Nat := [5, 1, 3, 2, 1, 2, 2, 2, 1, 1, 3]
def baseStart_3732662 : Nat := 118140960795 + 3732662 * 2 ^ 59
def prefixEnd_3732662 : Nat := 4983230072969 + 3 ^ 40 * 3732662 * 2
def baseEnd_3732662 : Nat := 1916649726772780176458807

theorem tailTrace_3732662 : CollatzResearch.WordTrace tailWord_3732662 prefixEnd_3732662 1916649726772780176458807 := by
  unfold tailWord_3732662
  simp only [CollatzResearch.WordTrace]
  refine ⟨8508835475200658547606515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 90760911735473691174469493 8508835475200658547606515)
  ·
    refine ⟨12763253212800987821409773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8508835475200658547606515 12763253212800987821409773)
    ·
      refine ⟨4786219954800370433028665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12763253212800987821409773 4786219954800370433028665)
      ·
        refine ⟨3589664966100277824771499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4786219954800370433028665 3589664966100277824771499)
        ·
          refine ⟨5384497449150416737157249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3589664966100277824771499 5384497449150416737157249)
          ·
            refine ⟨4038373086862812552867937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5384497449150416737157249 4038373086862812552867937)
            ·
              refine ⟨3028779815147109414650953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4038373086862812552867937 3028779815147109414650953)
              ·
                refine ⟨2271584861360332060988215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3028779815147109414650953 2271584861360332060988215)
                ·
                  refine ⟨3407377292040498091482323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2271584861360332060988215 3407377292040498091482323)
                  ·
                    refine ⟨5111065938060747137223485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3407377292040498091482323 5111065938060747137223485)
                    ·
                      refine ⟨1916649726772780176458807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5111065938060747137223485 1916649726772780176458807)
                      ·
                        rfl

theorem cell23_3732662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 2, 2, 2, 1, 1, 3].length) (baseStart_3732662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3732662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3732662 prefixEnd_3732662 := by exact prefixLift 3732662
  have htrace : WordTrace (prefixWord ++ tailWord_3732662) baseStart_3732662 baseEnd_3732662 := by
    simpa [prefixWord, tailWord_3732662, baseEnd_3732662] using wordTrace_append hprefix tailTrace_3732662
  have hstable : (prefixWord ++ tailWord_3732662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3732662).length < 2 ^ (prefixWord ++ tailWord_3732662).sum := by decide
  have hdescent : baseEnd_3732662 < baseStart_3732662 := by decide
  rcases family_descends (prefixWord ++ tailWord_3732662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3732668 : List Nat := [2, 2, 2, 3, 2, 1, 4, 2, 1, 2, 2]
def baseStart_3732668 : Nat := 118140960795 + 3732668 * 2 ^ 59
def prefixEnd_3732668 : Nat := 4983230072969 + 3 ^ 40 * 3732668 * 2
def baseEnd_3732668 : Nat := 1916652807656707152983779

theorem tailTrace_3732668 : CollatzResearch.WordTrace tailWord_3732668 prefixEnd_3732668 1916652807656707152983779 := by
  unfold tailWord_3732668
  simp only [CollatzResearch.WordTrace]
  refine ⟨68070793220594399893211329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90761057627459199857615105 68070793220594399893211329)
  ·
    refine ⟨51053094915445799919908497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68070793220594399893211329 51053094915445799919908497)
    ·
      refine ⟨38289821186584349939931373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51053094915445799919908497 38289821186584349939931373)
      ·
        refine ⟨14358682944969131227474265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38289821186584349939931373 14358682944969131227474265)
        ·
          refine ⟨10769012208726848420605699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14358682944969131227474265 10769012208726848420605699)
          ·
            refine ⟨16153518313090272630908549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10769012208726848420605699 16153518313090272630908549)
            ·
              refine ⟨3028784683704426118295353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16153518313090272630908549 3028784683704426118295353)
              ·
                refine ⟨2271588512778319588721515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3028784683704426118295353 2271588512778319588721515)
                ·
                  refine ⟨3407382769167479383082273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2271588512778319588721515 3407382769167479383082273)
                  ·
                    refine ⟨2555537076875609537311705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3407382769167479383082273 2555537076875609537311705)
                    ·
                      refine ⟨1916652807656707152983779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2555537076875609537311705 1916652807656707152983779)
                      ·
                        rfl

theorem cell23_3732668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 4, 2, 1, 2, 2].length) (baseStart_3732668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3732668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3732668 prefixEnd_3732668 := by exact prefixLift 3732668
  have htrace : WordTrace (prefixWord ++ tailWord_3732668) baseStart_3732668 baseEnd_3732668 := by
    simpa [prefixWord, tailWord_3732668, baseEnd_3732668] using wordTrace_append hprefix tailTrace_3732668
  have hstable : (prefixWord ++ tailWord_3732668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3732668).length < 2 ^ (prefixWord ++ tailWord_3732668).sum := by decide
  have hdescent : baseEnd_3732668 < baseStart_3732668 := by decide
  rcases family_descends (prefixWord ++ tailWord_3732668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3732670 : List Nat := [4, 2, 1, 1, 3, 1, 1, 1, 2, 7]
def baseStart_3732670 : Nat := 118140960795 + 3732670 * 2 ^ 59
def prefixEnd_3732670 : Nat := 4983230072969 + 3 ^ 40 * 3732670 * 2
def baseEnd_3732670 : Nat := 638884611539338715052923

theorem tailTrace_3732670 : CollatzResearch.WordTrace tailWord_3732670 prefixEnd_3732670 638884611539338715052923 := by
  unfold tailWord_3732670
  simp only [CollatzResearch.WordTrace]
  refine ⟨17017707423397694265999433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 90761106258121036085330309 17017707423397694265999433)
  ·
    refine ⟨12763280567548270699499575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17017707423397694265999433 12763280567548270699499575)
    ·
      refine ⟨19144920851322406049249363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12763280567548270699499575 19144920851322406049249363)
      ·
        refine ⟨28717381276983609073874045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19144920851322406049249363 28717381276983609073874045)
        ·
          refine ⟨10769017978868853402702767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28717381276983609073874045 10769017978868853402702767)
          ·
            refine ⟨16153526968303280104054151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10769017978868853402702767 16153526968303280104054151)
            ·
              refine ⟨24230290452454920156081227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16153526968303280104054151 24230290452454920156081227)
              ·
                refine ⟨36345435678682380234121841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24230290452454920156081227 36345435678682380234121841)
                ·
                  refine ⟨27259076759011785175591381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36345435678682380234121841 27259076759011785175591381)
                  ·
                    refine ⟨638884611539338715052923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 27259076759011785175591381 638884611539338715052923)
                    ·
                      rfl

theorem cell23_3732670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 1, 1, 2, 7].length) (baseStart_3732670 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3732670 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3732670 prefixEnd_3732670 := by exact prefixLift 3732670
  have htrace : WordTrace (prefixWord ++ tailWord_3732670) baseStart_3732670 baseEnd_3732670 := by
    simpa [prefixWord, tailWord_3732670, baseEnd_3732670] using wordTrace_append hprefix tailTrace_3732670
  have hstable : (prefixWord ++ tailWord_3732670).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3732670).length < 2 ^ (prefixWord ++ tailWord_3732670).sum := by decide
  have hdescent : baseEnd_3732670 < baseStart_3732670 := by decide
  rcases family_descends (prefixWord ++ tailWord_3732670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3732690 : List Nat := [3, 2, 2, 2, 1, 1, 1, 2, 2, 3, 4]
def baseStart_3732690 : Nat := 118140960795 + 3732690 * 2 ^ 59
def prefixEnd_3732690 : Nat := 4983230072969 + 3 ^ 40 * 3732690 * 2
def baseEnd_3732690 : Nat := 1916664104231106066908677

theorem tailTrace_3732690 : CollatzResearch.WordTrace tailWord_3732690 prefixEnd_3732690 1916664104231106066908677 := by
  unfold tailWord_3732690
  simp only [CollatzResearch.WordTrace]
  refine ⟨34035597211777274385930881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90761592564739398362482349 34035597211777274385930881)
  ·
    refine ⟨25526697908832955789448161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34035597211777274385930881 25526697908832955789448161)
    ·
      refine ⟨19145023431624716842086121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25526697908832955789448161 19145023431624716842086121)
      ·
        refine ⟨14358767573718537631564591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19145023431624716842086121 14358767573718537631564591)
        ·
          refine ⟨21538151360577806447346887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14358767573718537631564591 21538151360577806447346887)
          ·
            refine ⟨32307227040866709671020331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21538151360577806447346887 32307227040866709671020331)
            ·
              refine ⟨48460840561300064506530497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32307227040866709671020331 48460840561300064506530497)
              ·
                refine ⟨36345630420975048379897873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48460840561300064506530497 36345630420975048379897873)
                ·
                  refine ⟨27259222815731286284923405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36345630420975048379897873 27259222815731286284923405)
                  ·
                    refine ⟨10222208555899232356846277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27259222815731286284923405 10222208555899232356846277)
                    ·
                      refine ⟨1916664104231106066908677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10222208555899232356846277 1916664104231106066908677)
                      ·
                        rfl

theorem cell23_3732690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 2, 2, 3, 4].length) (baseStart_3732690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3732690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3732690 prefixEnd_3732690 := by exact prefixLift 3732690
  have htrace : WordTrace (prefixWord ++ tailWord_3732690) baseStart_3732690 baseEnd_3732690 := by
    simpa [prefixWord, tailWord_3732690, baseEnd_3732690] using wordTrace_append hprefix tailTrace_3732690
  have hstable : (prefixWord ++ tailWord_3732690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3732690).length < 2 ^ (prefixWord ++ tailWord_3732690).sum := by decide
  have hdescent : baseEnd_3732690 < baseStart_3732690 := by decide
  rcases family_descends (prefixWord ++ tailWord_3732690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3732711 : List Nat := [1, 1, 5, 3, 2, 1, 1, 3, 1, 3, 2]
def baseStart_3732711 : Nat := 118140960795 + 3732711 * 2 ^ 59
def prefixEnd_3732711 : Nat := 4983230072969 + 3 ^ 40 * 3732711 * 2
def baseEnd_3732711 : Nat := 1916674887324850484746081

theorem tailTrace_3732711 : CollatzResearch.WordTrace tailWord_3732711 prefixEnd_3732711 1916674887324850484746081 := by
  unfold tailWord_3732711
  simp only [CollatzResearch.WordTrace]
  refine ⟨136143154780033018130237987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90762103186688678753491991 136143154780033018130237987)
  ·
    refine ⟨204214732170049527195356981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136143154780033018130237987 204214732170049527195356981)
    ·
      refine ⟨19145131140942143174564717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 204214732170049527195356981 19145131140942143174564717)
      ·
        refine ⟨7179424177853303690461769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19145131140942143174564717 7179424177853303690461769)
        ·
          refine ⟨5384568133389977767846327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7179424177853303690461769 5384568133389977767846327)
          ·
            refine ⟨8076852200084966651769491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5384568133389977767846327 8076852200084966651769491)
            ·
              refine ⟨12115278300127449977654237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8076852200084966651769491 12115278300127449977654237)
              ·
                refine ⟨4543229362547793741620339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12115278300127449977654237 4543229362547793741620339)
                ·
                  refine ⟨6814844043821690612430509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4543229362547793741620339 6814844043821690612430509)
                  ·
                    refine ⟨2555566516433133979661441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6814844043821690612430509 2555566516433133979661441)
                    ·
                      refine ⟨1916674887324850484746081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2555566516433133979661441 1916674887324850484746081)
                      ·
                        rfl

theorem cell23_3732711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 1, 3, 1, 3, 2].length) (baseStart_3732711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3732711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3732711 prefixEnd_3732711 := by exact prefixLift 3732711
  have htrace : WordTrace (prefixWord ++ tailWord_3732711) baseStart_3732711 baseEnd_3732711 := by
    simpa [prefixWord, tailWord_3732711, baseEnd_3732711] using wordTrace_append hprefix tailTrace_3732711
  have hstable : (prefixWord ++ tailWord_3732711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3732711).length < 2 ^ (prefixWord ++ tailWord_3732711).sum := by decide
  have hdescent : baseEnd_3732711 < baseStart_3732711 := by decide
  rcases family_descends (prefixWord ++ tailWord_3732711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3732730 : List Nat := [3, 1, 1, 1, 1, 4, 4, 1, 7]
def baseStart_3732730 : Nat := 118140960795 + 3732730 * 2 ^ 59
def prefixEnd_3732730 : Nat := 4983230072969 + 3 ^ 40 * 3732730 * 2
def baseEnd_3732730 : Nat := 212964960384142878934277

theorem tailTrace_3732730 : CollatzResearch.WordTrace tailWord_3732730 prefixEnd_3732730 212964960384142878934277 := by
  unfold tailWord_3732730
  simp only [CollatzResearch.WordTrace]
  refine ⟨34035961941741046093794911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90762565177976122916786429 34035961941741046093794911)
  ·
    refine ⟨51053942912611569140692367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34035961941741046093794911 51053942912611569140692367)
    ·
      refine ⟨76580914368917353711038551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51053942912611569140692367 76580914368917353711038551)
      ·
        refine ⟨114871371553376030566557827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76580914368917353711038551 114871371553376030566557827)
        ·
          refine ⟨172307057330064045849836741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114871371553376030566557827 172307057330064045849836741)
          ·
            refine ⟨32307573249387008596844389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 172307057330064045849836741 32307573249387008596844389)
            ·
              refine ⟨6057669984260064111908323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32307573249387008596844389 6057669984260064111908323)
              ·
                refine ⟨9086504976390096167862485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6057669984260064111908323 9086504976390096167862485)
                ·
                  refine ⟨212964960384142878934277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9086504976390096167862485 212964960384142878934277)
                  ·
                    rfl

theorem cell23_3732730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 4, 1, 7].length) (baseStart_3732730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3732730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3732730 prefixEnd_3732730 := by exact prefixLift 3732730
  have htrace : WordTrace (prefixWord ++ tailWord_3732730) baseStart_3732730 baseEnd_3732730 := by
    simpa [prefixWord, tailWord_3732730, baseEnd_3732730] using wordTrace_append hprefix tailTrace_3732730
  have hstable : (prefixWord ++ tailWord_3732730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3732730).length < 2 ^ (prefixWord ++ tailWord_3732730).sum := by decide
  have hdescent : baseEnd_3732730 < baseStart_3732730 := by decide
  rcases family_descends (prefixWord ++ tailWord_3732730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3732741 : List Nat := [1, 3, 1, 1, 2, 1, 7, 1, 2, 2, 2]
def baseStart_3732741 : Nat := 118140960795 + 3732741 * 2 ^ 59
def prefixEnd_3732741 : Nat := 4983230072969 + 3 ^ 40 * 3732741 * 2
def baseEnd_3732741 : Nat := 1916690291744485367370943

theorem tailTrace_3732741 : CollatzResearch.WordTrace tailWord_3732741 prefixEnd_3732741 1916690291744485367370943 := by
  unfold tailWord_3732741
  simp only [CollatzResearch.WordTrace]
  refine ⟨136144248969924333253830077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90762832646616222169220051 136144248969924333253830077)
  ·
    refine ⟨51054093363721624970186279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 136144248969924333253830077 51054093363721624970186279)
    ·
      refine ⟨76581140045582437455279419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51054093363721624970186279 76581140045582437455279419)
      ·
        refine ⟨114871710068373656182919129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76581140045582437455279419 114871710068373656182919129)
        ·
          refine ⟨86153782551280242137189347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114871710068373656182919129 86153782551280242137189347)
          ·
            refine ⟨129230673826920363205784021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86153782551280242137189347 129230673826920363205784021)
            ·
              refine ⟨3028843917818446012635563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 129230673826920363205784021 3028843917818446012635563)
              ·
                refine ⟨4543265876727669018953345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3028843917818446012635563 4543265876727669018953345)
                ·
                  refine ⟨3407449407545751764215009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4543265876727669018953345 3407449407545751764215009)
                  ·
                    refine ⟨2555587055659313823161257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3407449407545751764215009 2555587055659313823161257)
                    ·
                      refine ⟨1916690291744485367370943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2555587055659313823161257 1916690291744485367370943)
                      ·
                        rfl

theorem cell23_3732741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 7, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 7, 1, 2, 2, 2].length) (baseStart_3732741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3732741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3732741 prefixEnd_3732741 := by exact prefixLift 3732741
  have htrace : WordTrace (prefixWord ++ tailWord_3732741) baseStart_3732741 baseEnd_3732741 := by
    simpa [prefixWord, tailWord_3732741, baseEnd_3732741] using wordTrace_append hprefix tailTrace_3732741
  have hstable : (prefixWord ++ tailWord_3732741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3732741).length < 2 ^ (prefixWord ++ tailWord_3732741).sum := by decide
  have hdescent : baseEnd_3732741 < baseStart_3732741 := by decide
  rcases family_descends (prefixWord ++ tailWord_3732741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3732760 : List Nat := [2, 1, 2, 3, 1, 3, 2, 1, 1, 7]
def baseStart_3732760 : Nat := 118140960795 + 3732760 * 2 ^ 59
def prefixEnd_3732760 : Nat := 4983230072969 + 3 ^ 40 * 3732760 * 2
def baseEnd_3732760 : Nat := 638900015958973597677785

theorem tailTrace_3732760 : CollatzResearch.WordTrace tailWord_3732760 prefixEnd_3732760 638900015958973597677785 := by
  unfold tailWord_3732760
  simp only [CollatzResearch.WordTrace]
  refine ⟨68072470978427749749385867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90763294637903666332514489 68072470978427749749385867)
  ·
    refine ⟨102108706467641624624078801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68072470978427749749385867 102108706467641624624078801)
    ·
      refine ⟨76581529850731218468059101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102108706467641624624078801 76581529850731218468059101)
      ·
        refine ⟨28718073694024206925522163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76581529850731218468059101 28718073694024206925522163)
        ·
          refine ⟨43077110541036310388283245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28718073694024206925522163 43077110541036310388283245)
          ·
            refine ⟨16153916452888616395606217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43077110541036310388283245 16153916452888616395606217)
            ·
              refine ⟨12115437339666462296704663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16153916452888616395606217 12115437339666462296704663)
              ·
                refine ⟨18173156009499693445056995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12115437339666462296704663 18173156009499693445056995)
                ·
                  refine ⟨27259734014249540167585493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18173156009499693445056995 27259734014249540167585493)
                  ·
                    refine ⟨638900015958973597677785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 27259734014249540167585493 638900015958973597677785)
                    ·
                      rfl

theorem cell23_3732760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 2, 1, 1, 7].length) (baseStart_3732760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3732760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3732760 prefixEnd_3732760 := by exact prefixLift 3732760
  have htrace : WordTrace (prefixWord ++ tailWord_3732760) baseStart_3732760 baseEnd_3732760 := by
    simpa [prefixWord, tailWord_3732760, baseEnd_3732760] using wordTrace_append hprefix tailTrace_3732760
  have hstable : (prefixWord ++ tailWord_3732760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3732760).length < 2 ^ (prefixWord ++ tailWord_3732760).sum := by decide
  have hdescent : baseEnd_3732760 < baseStart_3732760 := by decide
  rcases family_descends (prefixWord ++ tailWord_3732760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3732810 : List Nat := [3, 1, 2, 1, 1, 1, 1, 3, 2, 4, 4]
def baseStart_3732810 : Nat := 118140960795 + 3732810 * 2 ^ 59
def prefixEnd_3732810 : Nat := 4983230072969 + 3 ^ 40 * 3732810 * 2
def baseEnd_3732810 : Nat := 1916725721909645597408125

theorem tailTrace_3732810 : CollatzResearch.WordTrace tailWord_3732810 prefixEnd_3732810 1916725721909645597408125 := by
  unfold tailWord_3732810
  simp only [CollatzResearch.WordTrace]
  refine ⟨34036691401668589509522971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90764510404449572025394589 34036691401668589509522971)
  ·
    refine ⟨51055037102502884264284457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34036691401668589509522971 51055037102502884264284457)
    ·
      refine ⟨38291277826877163198213343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51055037102502884264284457 38291277826877163198213343)
      ·
        refine ⟨57436916740315744797320015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38291277826877163198213343 57436916740315744797320015)
        ·
          refine ⟨86155375110473617195980023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57436916740315744797320015 86155375110473617195980023)
          ·
            refine ⟨129233062665710425793970035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86155375110473617195980023 129233062665710425793970035)
            ·
              refine ⟨193849593998565638690955053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 129233062665710425793970035 193849593998565638690955053)
              ·
                refine ⟨72693597749462114509108145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 193849593998565638690955053 72693597749462114509108145)
                ·
                  refine ⟨54520198312096585881831109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 72693597749462114509108145 54520198312096585881831109)
                  ·
                    refine ⟨10222537183518109852843333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 54520198312096585881831109 10222537183518109852843333)
                    ·
                      refine ⟨1916725721909645597408125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10222537183518109852843333 1916725721909645597408125)
                      ·
                        rfl

theorem cell23_3732810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 3, 2, 4, 4].length) (baseStart_3732810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3732810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3732810 prefixEnd_3732810 := by exact prefixLift 3732810
  have htrace : WordTrace (prefixWord ++ tailWord_3732810) baseStart_3732810 baseEnd_3732810 := by
    simpa [prefixWord, tailWord_3732810, baseEnd_3732810] using wordTrace_append hprefix tailTrace_3732810
  have hstable : (prefixWord ++ tailWord_3732810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3732810).length < 2 ^ (prefixWord ++ tailWord_3732810).sum := by decide
  have hdescent : baseEnd_3732810 < baseStart_3732810 := by decide
  rcases family_descends (prefixWord ++ tailWord_3732810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3732824 : List Nat := [2, 1, 2, 2, 1, 1, 4, 5, 1, 4]
def baseStart_3732824 : Nat := 118140960795 + 3732824 * 2 ^ 59
def prefixEnd_3732824 : Nat := 4983230072969 + 3 ^ 40 * 3732824 * 2
def baseEnd_3732824 : Nat := 638910970212936180877687

theorem tailTrace_3732824 : CollatzResearch.WordTrace tailWord_3732824 prefixEnd_3732824 638910970212936180877687 := by
  unfold tailWord_3732824
  simp only [CollatzResearch.WordTrace]
  refine ⟨68073638114311819214550763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90764850819082425619401017 68073638114311819214550763)
  ·
    refine ⟨102110457171467728821826145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68073638114311819214550763 102110457171467728821826145)
    ·
      refine ⟨76582842878600796616369609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102110457171467728821826145 76582842878600796616369609)
      ·
        refine ⟨57437132158950597462277207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76582842878600796616369609 57437132158950597462277207)
        ·
          refine ⟨86155698238425896193415811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57437132158950597462277207 86155698238425896193415811)
          ·
            refine ⟨129233547357638844290123717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86155698238425896193415811 129233547357638844290123717)
            ·
              refine ⟨24231290129557283304398197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 129233547357638844290123717 24231290129557283304398197)
              ·
                refine ⟨2271683449645995309787331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24231290129557283304398197 2271683449645995309787331)
                ·
                  refine ⟨3407525174468992964680997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2271683449645995309787331 3407525174468992964680997)
                  ·
                    refine ⟨638910970212936180877687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3407525174468992964680997 638910970212936180877687)
                    ·
                      rfl

theorem cell23_3732824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 4, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 4, 5, 1, 4].length) (baseStart_3732824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3732824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3732824 prefixEnd_3732824 := by exact prefixLift 3732824
  have htrace : WordTrace (prefixWord ++ tailWord_3732824) baseStart_3732824 baseEnd_3732824 := by
    simpa [prefixWord, tailWord_3732824, baseEnd_3732824] using wordTrace_append hprefix tailTrace_3732824
  have hstable : (prefixWord ++ tailWord_3732824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3732824).length < 2 ^ (prefixWord ++ tailWord_3732824).sum := by decide
  have hdescent : baseEnd_3732824 < baseStart_3732824 := by decide
  rcases family_descends (prefixWord ++ tailWord_3732824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3732834 : List Nat := [3, 3, 2, 1, 1, 1, 1, 4, 2, 2, 3]
def baseStart_3732834 : Nat := 118140960795 + 3732834 * 2 ^ 59
def prefixEnd_3732834 : Nat := 4983230072969 + 3 ^ 40 * 3732834 * 2
def baseEnd_3732834 : Nat := 1916738045445353503508015

theorem tailTrace_3732834 : CollatzResearch.WordTrace tailWord_3732834 prefixEnd_3732834 1916738045445353503508015 := by
  unfold tailWord_3732834
  simp only [CollatzResearch.WordTrace]
  refine ⟨34036910239646852534241389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90765093972391606757977037 34036910239646852534241389)
  ·
    refine ⟨12763841339867569700340521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34036910239646852534241389 12763841339867569700340521)
    ·
      refine ⟨9572881004900677275255391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12763841339867569700340521 9572881004900677275255391)
      ·
        refine ⟨14359321507351015912883087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9572881004900677275255391 14359321507351015912883087)
        ·
          refine ⟨21538982261026523869324631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14359321507351015912883087 21538982261026523869324631)
          ·
            refine ⟨32308473391539785803986947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21538982261026523869324631 32308473391539785803986947)
            ·
              refine ⟨48462710087309678705980421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32308473391539785803986947 48462710087309678705980421)
              ·
                refine ⟨9086758141370564757371329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48462710087309678705980421 9086758141370564757371329)
                ·
                  refine ⟨6815068606027923568028497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9086758141370564757371329 6815068606027923568028497)
                  ·
                    refine ⟨5111301454520942676021373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6815068606027923568028497 5111301454520942676021373)
                    ·
                      refine ⟨1916738045445353503508015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5111301454520942676021373 1916738045445353503508015)
                      ·
                        rfl

theorem cell23_3732834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 4, 2, 2, 3].length) (baseStart_3732834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3732834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3732834 prefixEnd_3732834 := by exact prefixLift 3732834
  have htrace : WordTrace (prefixWord ++ tailWord_3732834) baseStart_3732834 baseEnd_3732834 := by
    simpa [prefixWord, tailWord_3732834, baseEnd_3732834] using wordTrace_append hprefix tailTrace_3732834
  have hstable : (prefixWord ++ tailWord_3732834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3732834).length < 2 ^ (prefixWord ++ tailWord_3732834).sum := by decide
  have hdescent : baseEnd_3732834 < baseStart_3732834 := by decide
  rcases family_descends (prefixWord ++ tailWord_3732834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3732837 : List Nat := [1, 3, 1, 3, 1, 2, 4, 2, 6]
def baseStart_3732837 : Nat := 118140960795 + 3732837 * 2 ^ 59
def prefixEnd_3732837 : Nat := 4983230072969 + 3 ^ 40 * 3732837 * 2
def baseEnd_3732837 : Nat := 212971065098590776863389

theorem tailTrace_3732837 : CollatzResearch.WordTrace tailWord_3732837 prefixEnd_3732837 212971065098590776863389 := by
  unfold tailWord_3732837
  simp only [CollatzResearch.WordTrace]
  refine ⟨136147750377576541649324765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90765166918384361099549843 136147750377576541649324765)
  ·
    refine ⟨51055406391591203118496787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 136147750377576541649324765 51055406391591203118496787)
    ·
      refine ⟨76583109587386804677745181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51055406391591203118496787 76583109587386804677745181)
      ·
        refine ⟨28718666095270051754154443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76583109587386804677745181 28718666095270051754154443)
        ·
          refine ⟨43077999142905077631231665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28718666095270051754154443 43077999142905077631231665)
          ·
            refine ⟨32308499357178808223423749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43077999142905077631231665 32308499357178808223423749)
            ·
              refine ⟨6057843629471026541891953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32308499357178808223423749 6057843629471026541891953)
              ·
                refine ⟨4543382722103269906418965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6057843629471026541891953 4543382722103269906418965)
                ·
                  refine ⟨212971065098590776863389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4543382722103269906418965 212971065098590776863389)
                  ·
                    rfl

theorem cell23_3732837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 4, 2, 6].length) (baseStart_3732837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3732837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3732837 prefixEnd_3732837 := by exact prefixLift 3732837
  have htrace : WordTrace (prefixWord ++ tailWord_3732837) baseStart_3732837 baseEnd_3732837 := by
    simpa [prefixWord, tailWord_3732837, baseEnd_3732837] using wordTrace_append hprefix tailTrace_3732837
  have hstable : (prefixWord ++ tailWord_3732837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3732837).length < 2 ^ (prefixWord ++ tailWord_3732837).sum := by decide
  have hdescent : baseEnd_3732837 < baseStart_3732837 := by decide
  rcases family_descends (prefixWord ++ tailWord_3732837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3732860 : List Nat := [2, 2, 2, 1, 1, 1, 3, 1, 2, 1, 7]
def baseStart_3732860 : Nat := 118140960795 + 3732860 * 2 ^ 59
def prefixEnd_3732860 : Nat := 4983230072969 + 3 ^ 40 * 3732860 * 2
def baseEnd_3732860 : Nat := 1916751395942370401782895

theorem tailTrace_3732860 : CollatzResearch.WordTrace tailWord_3732860 prefixEnd_3732860 1916751395942370401782895 := by
  unfold tailWord_3732860
  simp only [CollatzResearch.WordTrace]
  refine ⟨68074294628246608288706017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90765726170995477718274689 68074294628246608288706017)
  ·
    refine ⟨51055720971184956216529513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68074294628246608288706017 51055720971184956216529513)
    ·
      refine ⟨38291790728388717162397135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51055720971184956216529513 38291790728388717162397135)
      ·
        refine ⟨57437686092583075743595703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38291790728388717162397135 57437686092583075743595703)
        ·
          refine ⟨86156529138874613615393555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57437686092583075743595703 86156529138874613615393555)
          ·
            refine ⟨129234793708311920423090333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86156529138874613615393555 129234793708311920423090333)
            ·
              refine ⟨48463047640616970158658875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 129234793708311920423090333 48463047640616970158658875)
              ·
                refine ⟨72694571460925455237988313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48463047640616970158658875 72694571460925455237988313)
                ·
                  refine ⟨54520928595694091428491235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 72694571460925455237988313 54520928595694091428491235)
                  ·
                    refine ⟨81781392893541137142736853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 54520928595694091428491235 81781392893541137142736853)
                    ·
                      refine ⟨1916751395942370401782895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 81781392893541137142736853 1916751395942370401782895)
                      ·
                        rfl

theorem cell23_3732860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 1, 2, 1, 7].length) (baseStart_3732860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3732860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3732860 prefixEnd_3732860 := by exact prefixLift 3732860
  have htrace : WordTrace (prefixWord ++ tailWord_3732860) baseStart_3732860 baseEnd_3732860 := by
    simpa [prefixWord, tailWord_3732860, baseEnd_3732860] using wordTrace_append hprefix tailTrace_3732860
  have hstable : (prefixWord ++ tailWord_3732860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3732860).length < 2 ^ (prefixWord ++ tailWord_3732860).sum := by decide
  have hdescent : baseEnd_3732860 < baseStart_3732860 := by decide
  rcases family_descends (prefixWord ++ tailWord_3732860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3732867 : List Nat := [1, 1, 1, 3, 5, 1, 2, 1, 3, 5]
def baseStart_3732867 : Nat := 118140960795 + 3732867 * 2 ^ 59
def prefixEnd_3732867 : Nat := 4983230072969 + 3 ^ 40 * 3732867 * 2
def baseEnd_3732867 : Nat := 638918330102317291465121

theorem tailTrace_3732867 : CollatzResearch.WordTrace tailWord_3732867 prefixEnd_3732867 638918330102317291465121 := by
  unfold tailWord_3732867
  simp only [CollatzResearch.WordTrace]
  refine ⟨136148844567467856772916855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90765896378311904515277903 136148844567467856772916855)
  ·
    refine ⟨204223266851201785159375283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136148844567467856772916855 204223266851201785159375283)
    ·
      refine ⟨306334900276802677739062925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204223266851201785159375283 306334900276802677739062925)
      ·
        refine ⟨114875587603801004152148597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 306334900276802677739062925 114875587603801004152148597)
        ·
          refine ⟨10769586337856344139263931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 114875587603801004152148597 10769586337856344139263931)
          ·
            refine ⟨16154379506784516208895897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10769586337856344139263931 16154379506784516208895897)
            ·
              refine ⟨12115784630088387156671923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16154379506784516208895897 12115784630088387156671923)
              ·
                refine ⟨18173676945132580735007885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12115784630088387156671923 18173676945132580735007885)
                ·
                  refine ⟨6815128854424717775627957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18173676945132580735007885 6815128854424717775627957)
                  ·
                    refine ⟨638918330102317291465121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6815128854424717775627957 638918330102317291465121)
                    ·
                      rfl

theorem cell23_3732867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 2, 1, 3, 5].length) (baseStart_3732867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3732867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3732867 prefixEnd_3732867 := by exact prefixLift 3732867
  have htrace : WordTrace (prefixWord ++ tailWord_3732867) baseStart_3732867 baseEnd_3732867 := by
    simpa [prefixWord, tailWord_3732867, baseEnd_3732867] using wordTrace_append hprefix tailTrace_3732867
  have hstable : (prefixWord ++ tailWord_3732867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3732867).length < 2 ^ (prefixWord ++ tailWord_3732867).sum := by decide
  have hdescent : baseEnd_3732867 < baseStart_3732867 := by decide
  rcases family_descends (prefixWord ++ tailWord_3732867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3732898 : List Nat := [3, 3, 1, 2, 1, 2, 2, 4, 1, 1, 3]
def baseStart_3732898 : Nat := 118140960795 + 3732898 * 2 ^ 59
def prefixEnd_3732898 : Nat := 4983230072969 + 3 ^ 40 * 3732898 * 2
def baseEnd_3732898 : Nat := 1916770908207241253107721

theorem tailTrace_3732898 : CollatzResearch.WordTrace tailWord_3732898 prefixEnd_3732898 1916770908207241253107721 := by
  unfold tailWord_3732898
  simp only [CollatzResearch.WordTrace]
  refine ⟨34037493807588887266823837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90766650153570366044863565 34037493807588887266823837)
  ·
    refine ⟨12764060177845832725058939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34037493807588887266823837 12764060177845832725058939)
    ·
      refine ⟨19146090266768749087588409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12764060177845832725058939 19146090266768749087588409)
      ·
        refine ⟨14359567700076561815691307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19146090266768749087588409 14359567700076561815691307)
        ·
          refine ⟨21539351550114842723536961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14359567700076561815691307 21539351550114842723536961)
          ·
            refine ⟨16154513662586132042652721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21539351550114842723536961 16154513662586132042652721)
            ·
              refine ⟨12115885246939599031989541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16154513662586132042652721 12115885246939599031989541)
              ·
                refine ⟨2271728483801174818498039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12115885246939599031989541 2271728483801174818498039)
                ·
                  refine ⟨3407592725701762227747059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2271728483801174818498039 3407592725701762227747059)
                  ·
                    refine ⟨5111389088552643341620589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3407592725701762227747059 5111389088552643341620589)
                    ·
                      refine ⟨1916770908207241253107721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5111389088552643341620589 1916770908207241253107721)
                      ·
                        rfl

theorem cell23_3732898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 2, 4, 1, 1, 3].length) (baseStart_3732898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3732898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3732898 prefixEnd_3732898 := by exact prefixLift 3732898
  have htrace : WordTrace (prefixWord ++ tailWord_3732898) baseStart_3732898 baseEnd_3732898 := by
    simpa [prefixWord, tailWord_3732898, baseEnd_3732898] using wordTrace_append hprefix tailTrace_3732898
  have hstable : (prefixWord ++ tailWord_3732898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3732898).length < 2 ^ (prefixWord ++ tailWord_3732898).sum := by decide
  have hdescent : baseEnd_3732898 < baseStart_3732898 := by decide
  rcases family_descends (prefixWord ++ tailWord_3732898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3732921 : List Nat := [1, 2, 1, 4, 4, 1, 2, 2, 1, 1, 4]
def baseStart_3732921 : Nat := 118140960795 + 3732921 * 2 ^ 59
def prefixEnd_3732921 : Nat := 4983230072969 + 3 ^ 40 * 3732921 * 2
def baseEnd_3732921 : Nat := 1916782718262294663120115

theorem tailTrace_3732921 : CollatzResearch.WordTrace tailWord_3732921 prefixEnd_3732921 1916782718262294663120115 := by
  unfold tailWord_3732921
  simp only [CollatzResearch.WordTrace]
  refine ⟨136150814109272223995382617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90767209406181482663588411 136150814109272223995382617)
  ·
    refine ⟨102113110581954167996536963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136150814109272223995382617 102113110581954167996536963)
    ·
      refine ⟨153169665872931251994805445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102113110581954167996536963 153169665872931251994805445)
      ·
        refine ⟨28719312351174609749026021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 153169665872931251994805445 28719312351174609749026021)
        ·
          refine ⟨5384871065845239327942379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28719312351174609749026021 5384871065845239327942379)
          ·
            refine ⟨8077306598767858991913569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5384871065845239327942379 8077306598767858991913569)
            ·
              refine ⟨6057979949075894243935177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8077306598767858991913569 6057979949075894243935177)
              ·
                refine ⟨4543484961806920682951383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6057979949075894243935177 4543484961806920682951383)
                ·
                  refine ⟨6815227442710381024427075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4543484961806920682951383 6815227442710381024427075)
                  ·
                    refine ⟨10222841164065571536640613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6815227442710381024427075 10222841164065571536640613)
                    ·
                      refine ⟨1916782718262294663120115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10222841164065571536640613 1916782718262294663120115)
                      ·
                        rfl

theorem cell23_3732921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 2, 2, 1, 1, 4].length) (baseStart_3732921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3732921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3732921 prefixEnd_3732921 := by exact prefixLift 3732921
  have htrace : WordTrace (prefixWord ++ tailWord_3732921) baseStart_3732921 baseEnd_3732921 := by
    simpa [prefixWord, tailWord_3732921, baseEnd_3732921] using wordTrace_append hprefix tailTrace_3732921
  have hstable : (prefixWord ++ tailWord_3732921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3732921).length < 2 ^ (prefixWord ++ tailWord_3732921).sum := by decide
  have hdescent : baseEnd_3732921 < baseStart_3732921 := by decide
  rcases family_descends (prefixWord ++ tailWord_3732921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3732937 : List Nat := [1, 2, 1, 1, 2, 1, 3, 3, 3, 3, 3]
def baseStart_3732937 : Nat := 118140960795 + 3732937 * 2 ^ 59
def prefixEnd_3732937 : Nat := 4983230072969 + 3 ^ 40 * 3732937 * 2
def baseEnd_3732937 : Nat := 1916790933952766600520041

theorem tailTrace_3732937 : CollatzResearch.WordTrace tailWord_3732937 prefixEnd_3732937 1916790933952766600520041 := by
  unfold tailWord_3732937
  simp only [CollatzResearch.WordTrace]
  refine ⟨136151397677214258727965065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90767598451476172485310043 136151397677214258727965065)
  ·
    refine ⟨102113548257910694045973799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136151397677214258727965065 102113548257910694045973799)
    ·
      refine ⟨153170322386866041068960699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102113548257910694045973799 153170322386866041068960699)
      ·
        refine ⟨229755483580299061603441049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153170322386866041068960699 229755483580299061603441049)
        ·
          refine ⟨172316612685224296202580787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 229755483580299061603441049 172316612685224296202580787)
          ·
            refine ⟨258474919027836444303871181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 172316612685224296202580787 258474919027836444303871181)
            ·
              refine ⟨96928094635438666613951693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 258474919027836444303871181 96928094635438666613951693)
              ·
                refine ⟨36348035488289499980231885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 96928094635438666613951693 36348035488289499980231885)
                ·
                  refine ⟨13630513308108562492586957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36348035488289499980231885 13630513308108562492586957)
                  ·
                    refine ⟨5111442490540710934720109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13630513308108562492586957 5111442490540710934720109)
                    ·
                      refine ⟨1916790933952766600520041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5111442490540710934720109 1916790933952766600520041)
                      ·
                        rfl

theorem cell23_3732937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 3, 3, 3, 3].length) (baseStart_3732937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3732937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3732937 prefixEnd_3732937 := by exact prefixLift 3732937
  have htrace : WordTrace (prefixWord ++ tailWord_3732937) baseStart_3732937 baseEnd_3732937 := by
    simpa [prefixWord, tailWord_3732937, baseEnd_3732937] using wordTrace_append hprefix tailTrace_3732937
  have hstable : (prefixWord ++ tailWord_3732937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3732937).length < 2 ^ (prefixWord ++ tailWord_3732937).sum := by decide
  have hdescent : baseEnd_3732937 < baseStart_3732937 := by decide
  rcases family_descends (prefixWord ++ tailWord_3732937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3733022 : List Nat := [4, 3, 3, 1, 1, 1, 2, 1, 1, 3, 3]
def baseStart_3733022 : Nat := 118140960795 + 3733022 * 2 ^ 59
def prefixEnd_3733022 : Nat := 4983230072969 + 3 ^ 40 * 3733022 * 2
def baseEnd_3733022 : Nat := 1916834579808398767957151

theorem tailTrace_3733022 : CollatzResearch.WordTrace tailWord_3733022 prefixEnd_3733022 1916834579808398767957151 := by
  unfold tailWord_3733022
  simp only [CollatzResearch.WordTrace]
  refine ⟨17019312235238289780601165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 90769665254604212163206213 17019312235238289780601165)
  ·
    refine ⟨6382242088214358667725437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17019312235238289780601165 6382242088214358667725437)
    ·
      refine ⟨2393340783080384500397039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6382242088214358667725437 2393340783080384500397039)
      ·
        refine ⟨3590011174620576750595559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2393340783080384500397039 3590011174620576750595559)
        ·
          refine ⟨5385016761930865125893339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3590011174620576750595559 5385016761930865125893339)
          ·
            refine ⟨8077525142896297688840009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5385016761930865125893339 8077525142896297688840009)
            ·
              refine ⟨6058143857172223266630007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8077525142896297688840009 6058143857172223266630007)
              ·
                refine ⟨9087215785758334899945011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6058143857172223266630007 9087215785758334899945011)
                ·
                  refine ⟨13630823678637502349917517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9087215785758334899945011 13630823678637502349917517)
                  ·
                    refine ⟨5111558879489063381219069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13630823678637502349917517 5111558879489063381219069)
                    ·
                      refine ⟨1916834579808398767957151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5111558879489063381219069 1916834579808398767957151)
                      ·
                        rfl

theorem cell23_3733022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 2, 1, 1, 3, 3].length) (baseStart_3733022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3733022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3733022 prefixEnd_3733022 := by exact prefixLift 3733022
  have htrace : WordTrace (prefixWord ++ tailWord_3733022) baseStart_3733022 baseEnd_3733022 := by
    simpa [prefixWord, tailWord_3733022, baseEnd_3733022] using wordTrace_append hprefix tailTrace_3733022
  have hstable : (prefixWord ++ tailWord_3733022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3733022).length < 2 ^ (prefixWord ++ tailWord_3733022).sum := by decide
  have hdescent : baseEnd_3733022 < baseStart_3733022 := by decide
  rcases family_descends (prefixWord ++ tailWord_3733022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3733024 : List Nat := [2, 1, 1, 6, 1, 1, 1, 1, 1, 4, 4]
def baseStart_3733024 : Nat := 118140960795 + 3733024 * 2 ^ 59
def prefixEnd_3733024 : Nat := 4983230072969 + 3 ^ 40 * 3733024 * 2
def baseEnd_3733024 : Nat := 1916835606769707760132141

theorem tailTrace_3733024 : CollatzResearch.WordTrace tailWord_3733024 prefixEnd_3733024 1916835606769707760132141 := by
  unfold tailWord_3733024
  simp only [CollatzResearch.WordTrace]
  refine ⟨68077285413949536293191063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90769713885266048390921417 68077285413949536293191063)
  ·
    refine ⟨102115928120924304439786595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68077285413949536293191063 102115928120924304439786595)
    ·
      refine ⟨153173892181386456659679893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102115928120924304439786595 153173892181386456659679893)
      ·
        refine ⟨7180026196002490155922495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 153173892181386456659679893 7180026196002490155922495)
        ·
          refine ⟨10770039294003735233883743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7180026196002490155922495 10770039294003735233883743)
          ·
            refine ⟨16155058941005602850825615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10770039294003735233883743 16155058941005602850825615)
            ·
              refine ⟨24232588411508404276238423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16155058941005602850825615 24232588411508404276238423)
              ·
                refine ⟨36348882617262606414357635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24232588411508404276238423 36348882617262606414357635)
                ·
                  refine ⟨54523323925893909621536453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36348882617262606414357635 54523323925893909621536453)
                  ·
                    refine ⟨10223123236105108054038085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 54523323925893909621536453 10223123236105108054038085)
                    ·
                      refine ⟨1916835606769707760132141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10223123236105108054038085 1916835606769707760132141)
                      ·
                        rfl

theorem cell23_3733024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 1, 1, 1, 4, 4].length) (baseStart_3733024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3733024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3733024 prefixEnd_3733024 := by exact prefixLift 3733024
  have htrace : WordTrace (prefixWord ++ tailWord_3733024) baseStart_3733024 baseEnd_3733024 := by
    simpa [prefixWord, tailWord_3733024, baseEnd_3733024] using wordTrace_append hprefix tailTrace_3733024
  have hstable : (prefixWord ++ tailWord_3733024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3733024).length < 2 ^ (prefixWord ++ tailWord_3733024).sum := by decide
  have hdescent : baseEnd_3733024 < baseStart_3733024 := by decide
  rcases family_descends (prefixWord ++ tailWord_3733024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3733034 : List Nat := [3, 1, 4, 1, 1, 1, 3, 2, 7]
def baseStart_3733034 : Nat := 118140960795 + 3733034 * 2 ^ 59
def prefixEnd_3733034 : Nat := 4983230072969 + 3 ^ 40 * 3733034 * 2
def baseEnd_3733034 : Nat := 212982304619583635667455

theorem tailTrace_3733034 : CollatzResearch.WordTrace tailWord_3733034 prefixEnd_3733034 212982304619583635667455 := by
  unfold tailWord_3733034
  simp only [CollatzResearch.WordTrace]
  refine ⟨34038733889465711073561539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90769957038575229529497437 34038733889465711073561539)
  ·
    refine ⟨51058100834198566610342309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34038733889465711073561539 51058100834198566610342309)
    ·
      refine ⟨9573393906412231239439183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 51058100834198566610342309 9573393906412231239439183)
      ·
        refine ⟨14360090859618346859158775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9573393906412231239439183 14360090859618346859158775)
        ·
          refine ⟨21540136289427520288738163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14360090859618346859158775 21540136289427520288738163)
          ·
            refine ⟨32310204434141280433107245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21540136289427520288738163 32310204434141280433107245)
            ·
              refine ⟨12116326662802980162415217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32310204434141280433107245 12116326662802980162415217)
              ·
                refine ⟨9087244997102235121811413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12116326662802980162415217 9087244997102235121811413)
                ·
                  refine ⟨212982304619583635667455, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9087244997102235121811413 212982304619583635667455)
                  ·
                    rfl

theorem cell23_3733034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 3, 2, 7].length) (baseStart_3733034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3733034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3733034 prefixEnd_3733034 := by exact prefixLift 3733034
  have htrace : WordTrace (prefixWord ++ tailWord_3733034) baseStart_3733034 baseEnd_3733034 := by
    simpa [prefixWord, tailWord_3733034, baseEnd_3733034] using wordTrace_append hprefix tailTrace_3733034
  have hstable : (prefixWord ++ tailWord_3733034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3733034).length < 2 ^ (prefixWord ++ tailWord_3733034).sum := by decide
  have hdescent : baseEnd_3733034 < baseStart_3733034 := by decide
  rcases family_descends (prefixWord ++ tailWord_3733034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3733062 : List Nat := [6, 1, 1, 1, 3, 1, 1, 1, 4, 2, 2]
def baseStart_3733062 : Nat := 118140960795 + 3733062 * 2 ^ 59
def prefixEnd_3733062 : Nat := 4983230072969 + 3 ^ 40 * 3733062 * 2
def baseEnd_3733062 : Nat := 1916855119034578611456967

theorem tailTrace_3733062 : CollatzResearch.WordTrace tailWord_3733062 prefixEnd_3733062 1916855119034578611456967 := by
  unfold tailWord_3733062
  simp only [CollatzResearch.WordTrace]
  refine ⟨4254873650055043908633295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 90770637867840936717510293 4254873650055043908633295)
  ·
    refine ⟨6382310475082565862949943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4254873650055043908633295 6382310475082565862949943)
    ·
      refine ⟨9573465712623848794424915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6382310475082565862949943 9573465712623848794424915)
      ·
        refine ⟨14360198568935773191637373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9573465712623848794424915 14360198568935773191637373)
        ·
          refine ⟨5385074463350914946864015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14360198568935773191637373 5385074463350914946864015)
          ·
            refine ⟨8077611695026372420296023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5385074463350914946864015 8077611695026372420296023)
            ·
              refine ⟨12116417542539558630444035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8077611695026372420296023 12116417542539558630444035)
              ·
                refine ⟨18174626313809337945666053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12116417542539558630444035 18174626313809337945666053)
                ·
                  refine ⟨3407742433839250864812385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18174626313809337945666053 3407742433839250864812385)
                  ·
                    refine ⟨2555806825379438148609289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3407742433839250864812385 2555806825379438148609289)
                    ·
                      refine ⟨1916855119034578611456967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2555806825379438148609289 1916855119034578611456967)
                      ·
                        rfl

theorem cell23_3733062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 1, 1, 4, 2, 2].length) (baseStart_3733062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3733062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3733062 prefixEnd_3733062 := by exact prefixLift 3733062
  have htrace : WordTrace (prefixWord ++ tailWord_3733062) baseStart_3733062 baseEnd_3733062 := by
    simpa [prefixWord, tailWord_3733062, baseEnd_3733062] using wordTrace_append hprefix tailTrace_3733062
  have hstable : (prefixWord ++ tailWord_3733062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3733062).length < 2 ^ (prefixWord ++ tailWord_3733062).sum := by decide
  have hdescent : baseEnd_3733062 < baseStart_3733062 := by decide
  rcases family_descends (prefixWord ++ tailWord_3733062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3733121 : List Nat := [1, 2, 4, 2, 1, 2, 1, 1, 4, 2, 3]
def baseStart_3733121 : Nat := 118140960795 + 3733121 * 2 ^ 59
def prefixEnd_3733121 : Nat := 4983230072969 + 3 ^ 40 * 3733121 * 2
def baseEnd_3733121 : Nat := 1916885414393193880619195

theorem tailTrace_3733121 : CollatzResearch.WordTrace tailWord_3733121 prefixEnd_3733121 1916885414393193880619195 := by
  unfold tailWord_3733121
  simp only [CollatzResearch.WordTrace]
  refine ⟨136158108708547658152663217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90772072472365105435108811 136158108708547658152663217)
  ·
    refine ⟨102118581531410743614497413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136158108708547658152663217 102118581531410743614497413)
    ·
      refine ⟨19147234037139514427718265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 102118581531410743614497413 19147234037139514427718265)
      ·
        refine ⟨14360425527854635820788699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19147234037139514427718265 14360425527854635820788699)
        ·
          refine ⟨21540638291781953731183049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14360425527854635820788699 21540638291781953731183049)
          ·
            refine ⟨16155478718836465298387287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21540638291781953731183049 16155478718836465298387287)
            ·
              refine ⟨24233218078254697947580931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16155478718836465298387287 24233218078254697947580931)
              ·
                refine ⟨36349827117382046921371397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24233218078254697947580931 36349827117382046921371397)
                ·
                  refine ⟨6815592584509133797757137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36349827117382046921371397 6815592584509133797757137)
                  ·
                    refine ⟨5111694438381850348317853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6815592584509133797757137 5111694438381850348317853)
                    ·
                      refine ⟨1916885414393193880619195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5111694438381850348317853 1916885414393193880619195)
                      ·
                        rfl

theorem cell23_3733121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 1, 1, 4, 2, 3].length) (baseStart_3733121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3733121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3733121 prefixEnd_3733121 := by exact prefixLift 3733121
  have htrace : WordTrace (prefixWord ++ tailWord_3733121) baseStart_3733121 baseEnd_3733121 := by
    simpa [prefixWord, tailWord_3733121, baseEnd_3733121] using wordTrace_append hprefix tailTrace_3733121
  have hstable : (prefixWord ++ tailWord_3733121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3733121).length < 2 ^ (prefixWord ++ tailWord_3733121).sum := by decide
  have hdescent : baseEnd_3733121 < baseStart_3733121 := by decide
  rcases family_descends (prefixWord ++ tailWord_3733121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3733178 : List Nat := [3, 1, 1, 1, 2, 4, 2, 2, 2, 3, 2]
def baseStart_3733178 : Nat := 118140960795 + 3733178 * 2 ^ 59
def prefixEnd_3733178 : Nat := 4983230072969 + 3 ^ 40 * 3733178 * 2
def baseEnd_3733178 : Nat := 1916914682790500157606433

theorem tailTrace_3733178 : CollatzResearch.WordTrace tailWord_3733178 prefixEnd_3733178 1916914682790500157606433 := by
  unfold tailWord_3733178
  simp only [CollatzResearch.WordTrace]
  refine ⟨34040046917335289221872047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90773458446227437924992125 34040046917335289221872047)
  ·
    refine ⟨51060070376002933832808071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34040046917335289221872047 51060070376002933832808071)
    ·
      refine ⟨76590105564004400749212107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51060070376002933832808071 76590105564004400749212107)
      ·
        refine ⟨114885158346006601123818161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76590105564004400749212107 114885158346006601123818161)
        ·
          refine ⟨86163868759504950842863621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114885158346006601123818161 86163868759504950842863621)
          ·
            refine ⟨16155725392407178283036929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 86163868759504950842863621 16155725392407178283036929)
            ·
              refine ⟨12116794044305383712277697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16155725392407178283036929 12116794044305383712277697)
              ·
                refine ⟨9087595533229037784208273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12116794044305383712277697 9087595533229037784208273)
                ·
                  refine ⟨6815696649921778338156205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9087595533229037784208273 6815696649921778338156205)
                  ·
                    refine ⟨2555886243720666876808577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6815696649921778338156205 2555886243720666876808577)
                    ·
                      refine ⟨1916914682790500157606433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2555886243720666876808577 1916914682790500157606433)
                      ·
                        rfl

theorem cell23_3733178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 2, 2, 2, 3, 2].length) (baseStart_3733178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3733178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3733178 prefixEnd_3733178 := by exact prefixLift 3733178
  have htrace : WordTrace (prefixWord ++ tailWord_3733178) baseStart_3733178 baseEnd_3733178 := by
    simpa [prefixWord, tailWord_3733178, baseEnd_3733178] using wordTrace_append hprefix tailTrace_3733178
  have hstable : (prefixWord ++ tailWord_3733178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3733178).length < 2 ^ (prefixWord ++ tailWord_3733178).sum := by decide
  have hdescent : baseEnd_3733178 < baseStart_3733178 := by decide
  rcases family_descends (prefixWord ++ tailWord_3733178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3733184 : List Nat := [2, 1, 1, 2, 4, 1, 1, 2, 3, 6]
def baseStart_3733184 : Nat := 118140960795 + 3733184 * 2 ^ 59
def prefixEnd_3733184 : Nat := 4983230072969 + 3 ^ 40 * 3733184 * 2
def baseEnd_3733184 : Nat := 638972587891475711377135

theorem tailTrace_3733184 : CollatzResearch.WordTrace tailWord_3733184 prefixEnd_3733184 638972587891475711377135 := by
  unfold tailWord_3733184
  simp only [CollatzResearch.WordTrace]
  refine ⟨68080203253659709956103303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90773604338212946608137737 68080203253659709956103303)
  ·
    refine ⟨102120304880489564934154955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68080203253659709956103303 102120304880489564934154955)
    ·
      refine ⟨153180457320734347401232433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102120304880489564934154955 153180457320734347401232433)
      ·
        refine ⟨114885342990550760550924325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 153180457320734347401232433 114885342990550760550924325)
        ·
          refine ⟨21541001810728267603298311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 114885342990550760550924325 21541001810728267603298311)
          ·
            refine ⟨32311502716092401404947467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21541001810728267603298311 32311502716092401404947467)
            ·
              refine ⟨48467254074138602107421201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32311502716092401404947467 48467254074138602107421201)
              ·
                refine ⟨36350440555603951580565901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48467254074138602107421201 36350440555603951580565901)
                ·
                  refine ⟨13631415208351481842712213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36350440555603951580565901 13631415208351481842712213)
                  ·
                    refine ⟨638972587891475711377135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13631415208351481842712213 638972587891475711377135)
                    ·
                      rfl

theorem cell23_3733184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 2, 3, 6].length) (baseStart_3733184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3733184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3733184 prefixEnd_3733184 := by exact prefixLift 3733184
  have htrace : WordTrace (prefixWord ++ tailWord_3733184) baseStart_3733184 baseEnd_3733184 := by
    simpa [prefixWord, tailWord_3733184, baseEnd_3733184] using wordTrace_append hprefix tailTrace_3733184
  have hstable : (prefixWord ++ tailWord_3733184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3733184).length < 2 ^ (prefixWord ++ tailWord_3733184).sum := by decide
  have hdescent : baseEnd_3733184 < baseStart_3733184 := by decide
  rcases family_descends (prefixWord ++ tailWord_3733184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3733201 : List Nat := [1, 2, 2, 1, 2, 5, 2, 1, 1, 6]
def baseStart_3733201 : Nat := 118140960795 + 3733201 * 2 ^ 59
def prefixEnd_3733201 : Nat := 4983230072969 + 3 ^ 40 * 3733201 * 2
def baseEnd_3733201 : Nat := 638975497615184522539609

theorem tailTrace_3733201 : CollatzResearch.WordTrace tailWord_3733201 prefixEnd_3733201 638975497615184522539609 := by
  unfold tailWord_3733201
  simp only [CollatzResearch.WordTrace]
  refine ⟨136161026548257831815575457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90774017698838554543716971 136161026548257831815575457)
  ·
    refine ⟨102120769911193373861681593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136161026548257831815575457 102120769911193373861681593)
    ·
      refine ⟨76590577433395030396261195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102120769911193373861681593 76590577433395030396261195)
      ·
        refine ⟨114885866150092545594391793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76590577433395030396261195 114885866150092545594391793)
        ·
          refine ⟨86164399612569409195793845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114885866150092545594391793 86164399612569409195793845)
          ·
            refine ⟨8077912463678382112105673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 86164399612569409195793845 8077912463678382112105673)
            ·
              refine ⟨6058434347758786584079255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8077912463678382112105673 6058434347758786584079255)
              ·
                refine ⟨9087651521638179876118883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6058434347758786584079255 9087651521638179876118883)
                ·
                  refine ⟨13631477282457269814178325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9087651521638179876118883 13631477282457269814178325)
                  ·
                    refine ⟨638975497615184522539609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13631477282457269814178325 638975497615184522539609)
                    ·
                      rfl

theorem cell23_3733201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 2, 1, 1, 6].length) (baseStart_3733201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3733201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3733201 prefixEnd_3733201 := by exact prefixLift 3733201
  have htrace : WordTrace (prefixWord ++ tailWord_3733201) baseStart_3733201 baseEnd_3733201 := by
    simpa [prefixWord, tailWord_3733201, baseEnd_3733201] using wordTrace_append hprefix tailTrace_3733201
  have hstable : (prefixWord ++ tailWord_3733201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3733201).length < 2 ^ (prefixWord ++ tailWord_3733201).sum := by decide
  have hdescent : baseEnd_3733201 < baseStart_3733201 := by decide
  rcases family_descends (prefixWord ++ tailWord_3733201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3733221 : List Nat := [1, 3, 1, 4, 1, 1, 1, 4, 1, 2, 4]
def baseStart_3733221 : Nat := 118140960795 + 3733221 * 2 ^ 59
def prefixEnd_3733221 : Nat := 4983230072969 + 3 ^ 40 * 3733221 * 2
def baseEnd_3733221 : Nat := 1916936762458643489368735

theorem tailTrace_3733221 : CollatzResearch.WordTrace tailWord_3733221 prefixEnd_3733221 1916936762458643489368735 := by
  unfold tailWord_3733221
  simp only [CollatzResearch.WordTrace]
  refine ⟨136161756008185375231303517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90774504005456916820869011 136161756008185375231303517)
  ·
    refine ⟨51060658503069515711738819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 136161756008185375231303517 51060658503069515711738819)
    ·
      refine ⟨76590987754604273567608229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51060658503069515711738819 76590987754604273567608229)
      ·
        refine ⟨14360810203988301293926543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 76590987754604273567608229 14360810203988301293926543)
        ·
          refine ⟨21541215305982451940889815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14360810203988301293926543 21541215305982451940889815)
          ·
            refine ⟨32311822958973677911334723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21541215305982451940889815 32311822958973677911334723)
            ·
              refine ⟨48467734438460516867002085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32311822958973677911334723 48467734438460516867002085)
              ·
                refine ⟨9087700207211346912562891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48467734438460516867002085 9087700207211346912562891)
                ·
                  refine ⟨13631550310817020368844337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9087700207211346912562891 13631550310817020368844337)
                  ·
                    refine ⟨10223662733112765276633253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13631550310817020368844337 10223662733112765276633253)
                    ·
                      refine ⟨1916936762458643489368735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10223662733112765276633253 1916936762458643489368735)
                      ·
                        rfl

theorem cell23_3733221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 4, 1, 2, 4].length) (baseStart_3733221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3733221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3733221 prefixEnd_3733221 := by exact prefixLift 3733221
  have htrace : WordTrace (prefixWord ++ tailWord_3733221) baseStart_3733221 baseEnd_3733221 := by
    simpa [prefixWord, tailWord_3733221, baseEnd_3733221] using wordTrace_append hprefix tailTrace_3733221
  have hstable : (prefixWord ++ tailWord_3733221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3733221).length < 2 ^ (prefixWord ++ tailWord_3733221).sum := by decide
  have hdescent : baseEnd_3733221 < baseStart_3733221 := by decide
  rcases family_descends (prefixWord ++ tailWord_3733221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3733255 : List Nat := [1, 1, 4, 4, 2, 2, 1, 1, 1, 2, 4]
def baseStart_3733255 : Nat := 118140960795 + 3733255 * 2 ^ 59
def prefixEnd_3733255 : Nat := 4983230072969 + 3 ^ 40 * 3733255 * 2
def baseEnd_3733255 : Nat := 1916954220800896356343579

theorem tailTrace_3733255 : CollatzResearch.WordTrace tailWord_3733255 prefixEnd_3733255 1916954220800896356343579 := by
  unfold tailWord_3733255
  simp only [CollatzResearch.WordTrace]
  refine ⟨136162996090062199038041219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90775330726708132692027479 136162996090062199038041219)
  ·
    refine ⟨204244494135093298557061829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136162996090062199038041219 204244494135093298557061829)
    ·
      refine ⟨38295842650329993479449093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 204244494135093298557061829 38295842650329993479449093)
      ·
        refine ⟨7180470496936873777396705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38295842650329993479449093 7180470496936873777396705)
        ·
          refine ⟨5385352872702655333047529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7180470496936873777396705 5385352872702655333047529)
          ·
            refine ⟨4039014654526991499785647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5385352872702655333047529 4039014654526991499785647)
            ·
              refine ⟨6058521981790487249678471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4039014654526991499785647 6058521981790487249678471)
              ·
                refine ⟨9087782972685730874517707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6058521981790487249678471 9087782972685730874517707)
                ·
                  refine ⟨13631674459028596311776561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9087782972685730874517707 13631674459028596311776561)
                  ·
                    refine ⟨10223755844271447233832421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13631674459028596311776561 10223755844271447233832421)
                    ·
                      refine ⟨1916954220800896356343579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10223755844271447233832421 1916954220800896356343579)
                      ·
                        rfl

theorem cell23_3733255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 2, 1, 1, 1, 2, 4].length) (baseStart_3733255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3733255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3733255 prefixEnd_3733255 := by exact prefixLift 3733255
  have htrace : WordTrace (prefixWord ++ tailWord_3733255) baseStart_3733255 baseEnd_3733255 := by
    simpa [prefixWord, tailWord_3733255, baseEnd_3733255] using wordTrace_append hprefix tailTrace_3733255
  have hstable : (prefixWord ++ tailWord_3733255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3733255).length < 2 ^ (prefixWord ++ tailWord_3733255).sum := by decide
  have hdescent : baseEnd_3733255 < baseStart_3733255 := by decide
  rcases family_descends (prefixWord ++ tailWord_3733255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3733258 : List Nat := [3, 1, 2, 2, 1, 3, 3, 1, 1, 3, 3]
def baseStart_3733258 : Nat := 118140960795 + 3733258 * 2 ^ 59
def prefixEnd_3733258 : Nat := 4983230072969 + 3 ^ 40 * 3733258 * 2
def baseEnd_3733258 : Nat := 1916955761242859844606065

theorem tailTrace_3733258 : CollatzResearch.WordTrace tailWord_3733258 prefixEnd_3733258 1916955761242859844606065 := by
  unfold tailWord_3733258
  simp only [CollatzResearch.WordTrace]
  refine ⟨34040776377262832637600107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90775403672700887033600285 34040776377262832637600107)
  ·
    refine ⟨51061164565894248956400161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34040776377262832637600107 51061164565894248956400161)
    ·
      refine ⟨38295873424420686717300121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51061164565894248956400161 38295873424420686717300121)
      ·
        refine ⟨28721905068315515037975091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38295873424420686717300121 28721905068315515037975091)
        ·
          refine ⟨43082857602473272556962637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28721905068315515037975091 43082857602473272556962637)
          ·
            refine ⟨16156071600927477208860989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43082857602473272556962637 16156071600927477208860989)
            ·
              refine ⟨6058526850347803953322871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16156071600927477208860989 6058526850347803953322871)
              ·
                refine ⟨9087790275521705929984307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6058526850347803953322871 9087790275521705929984307)
                ·
                  refine ⟨13631685413282558894976461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9087790275521705929984307 13631685413282558894976461)
                  ·
                    refine ⟨5111882029980959585616173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13631685413282558894976461 5111882029980959585616173)
                    ·
                      refine ⟨1916955761242859844606065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5111882029980959585616173 1916955761242859844606065)
                      ·
                        rfl

theorem cell23_3733258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 3, 1, 1, 3, 3].length) (baseStart_3733258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3733258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3733258 prefixEnd_3733258 := by exact prefixLift 3733258
  have htrace : WordTrace (prefixWord ++ tailWord_3733258) baseStart_3733258 baseEnd_3733258 := by
    simpa [prefixWord, tailWord_3733258, baseEnd_3733258] using wordTrace_append hprefix tailTrace_3733258
  have hstable : (prefixWord ++ tailWord_3733258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3733258).length < 2 ^ (prefixWord ++ tailWord_3733258).sum := by decide
  have hdescent : baseEnd_3733258 < baseStart_3733258 := by decide
  rcases family_descends (prefixWord ++ tailWord_3733258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3733271 : List Nat := [1, 1, 3, 4, 2, 1, 1, 1, 2, 2, 5]
def baseStart_3733271 : Nat := 118140960795 + 3733271 * 2 ^ 59
def prefixEnd_3733271 : Nat := 4983230072969 + 3 ^ 40 * 3733271 * 2
def baseEnd_3733271 : Nat := 1916962436491368293743505

theorem tailTrace_3733271 : CollatzResearch.WordTrace tailWord_3733271 prefixEnd_3733271 1916962436491368293743505 := by
  unfold tailWord_3733271
  simp only [CollatzResearch.WordTrace]
  refine ⟨136163579658004233770623667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90775719772002822513749111 136163579658004233770623667)
  ·
    refine ⟨204245369487006350655935501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136163579658004233770623667 204245369487006350655935501)
    ·
      refine ⟨76592013557627381495975813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 204245369487006350655935501 76592013557627381495975813)
      ·
        refine ⟨14361002542055134030495465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 76592013557627381495975813 14361002542055134030495465)
        ·
          refine ⟨10770751906541350522871599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14361002542055134030495465 10770751906541350522871599)
          ·
            refine ⟨16156127859812025784307399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10770751906541350522871599 16156127859812025784307399)
            ·
              refine ⟨24234191789718038676461099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16156127859812025784307399 24234191789718038676461099)
              ·
                refine ⟨36351287684577058014691649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24234191789718038676461099 36351287684577058014691649)
                ·
                  refine ⟨27263465763432793511018737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36351287684577058014691649 27263465763432793511018737)
                  ·
                    refine ⟨20447599322574595133264053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27263465763432793511018737 20447599322574595133264053)
                    ·
                      refine ⟨1916962436491368293743505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20447599322574595133264053 1916962436491368293743505)
                      ·
                        rfl

theorem cell23_3733271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 1, 1, 2, 2, 5].length) (baseStart_3733271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3733271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3733271 prefixEnd_3733271 := by exact prefixLift 3733271
  have htrace : WordTrace (prefixWord ++ tailWord_3733271) baseStart_3733271 baseEnd_3733271 := by
    simpa [prefixWord, tailWord_3733271, baseEnd_3733271] using wordTrace_append hprefix tailTrace_3733271
  have hstable : (prefixWord ++ tailWord_3733271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3733271).length < 2 ^ (prefixWord ++ tailWord_3733271).sum := by decide
  have hdescent : baseEnd_3733271 < baseStart_3733271 := by decide
  rcases family_descends (prefixWord ++ tailWord_3733271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3733285 : List Nat := [1, 3, 1, 2, 3, 2, 2, 3, 1, 3, 2]
def baseStart_3733285 : Nat := 118140960795 + 3733285 * 2 ^ 59
def prefixEnd_3733285 : Nat := 4983230072969 + 3 ^ 40 * 3733285 * 2
def baseEnd_3733285 : Nat := 1916969625220531238968441

theorem tailTrace_3733285 : CollatzResearch.WordTrace tailWord_3733285 prefixEnd_3733285 1916969625220531238968441 := by
  unfold tailWord_3733285
  simp only [CollatzResearch.WordTrace]
  refine ⟨136164090279953514161633309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90776060186635676107755539 136164090279953514161633309)
  ·
    refine ⟨51061533854982567810612491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 136164090279953514161633309 51061533854982567810612491)
    ·
      refine ⟨76592300782473851715918737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51061533854982567810612491 76592300782473851715918737)
      ·
        refine ⟨57444225586855388786939053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76592300782473851715918737 57444225586855388786939053)
        ·
          refine ⟨21541584595070770795102145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57444225586855388786939053 21541584595070770795102145)
          ·
            refine ⟨16156188446303078096326609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21541584595070770795102145 16156188446303078096326609)
            ·
              refine ⟨12117141334727308572244957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16156188446303078096326609 12117141334727308572244957)
              ·
                refine ⟨4543928000522740714591859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12117141334727308572244957 4543928000522740714591859)
                ·
                  refine ⟨6815892000784111071887789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4543928000522740714591859 6815892000784111071887789)
                  ·
                    refine ⟨2555959500294041651957921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6815892000784111071887789 2555959500294041651957921)
                    ·
                      refine ⟨1916969625220531238968441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2555959500294041651957921 1916969625220531238968441)
                      ·
                        rfl

theorem cell23_3733285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 2, 3, 1, 3, 2].length) (baseStart_3733285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3733285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3733285 prefixEnd_3733285 := by exact prefixLift 3733285
  have htrace : WordTrace (prefixWord ++ tailWord_3733285) baseStart_3733285 baseEnd_3733285 := by
    simpa [prefixWord, tailWord_3733285, baseEnd_3733285] using wordTrace_append hprefix tailTrace_3733285
  have hstable : (prefixWord ++ tailWord_3733285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3733285).length < 2 ^ (prefixWord ++ tailWord_3733285).sum := by decide
  have hdescent : baseEnd_3733285 < baseStart_3733285 := by decide
  rcases family_descends (prefixWord ++ tailWord_3733285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3733309 : List Nat := [1, 4, 1, 4, 1, 3, 2, 1, 2, 1, 3]
def baseStart_3733309 : Nat := 118140960795 + 3733309 * 2 ^ 59
def prefixEnd_3733309 : Nat := 4983230072969 + 3 ^ 40 * 3733309 * 2
def baseEnd_3733309 : Nat := 1916981948756239145068331

theorem tailTrace_3733309 : CollatzResearch.WordTrace tailWord_3733309 prefixEnd_3733309 1916981948756239145068331 := by
  unfold tailWord_3733309
  simp only [CollatzResearch.WordTrace]
  refine ⟨136164965631866566260506981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90776643754577710840337987 136164965631866566260506981)
  ·
    refine ⟨25530931055974981173845059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 136164965631866566260506981 25530931055974981173845059)
    ·
      refine ⟨38296396583962471760767589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25530931055974981173845059 38296396583962471760767589)
      ·
        refine ⟨7180574359492963455143923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38296396583962471760767589 7180574359492963455143923)
        ·
          refine ⟨10770861539239445182715885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7180574359492963455143923 10770861539239445182715885)
          ·
            refine ⟨4039073077214791943518457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10770861539239445182715885 4039073077214791943518457)
            ·
              refine ⟨3029304807911093957638843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4039073077214791943518457 3029304807911093957638843)
              ·
                refine ⟨4543957211866640936458265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3029304807911093957638843 4543957211866640936458265)
                ·
                  refine ⟨3407967908899980702343699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4543957211866640936458265 3407967908899980702343699)
                  ·
                    refine ⟨5111951863349971053515549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3407967908899980702343699 5111951863349971053515549)
                    ·
                      refine ⟨1916981948756239145068331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5111951863349971053515549 1916981948756239145068331)
                      ·
                        rfl

theorem cell23_3733309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 3, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 3, 2, 1, 2, 1, 3].length) (baseStart_3733309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3733309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3733309 prefixEnd_3733309 := by exact prefixLift 3733309
  have htrace : WordTrace (prefixWord ++ tailWord_3733309) baseStart_3733309 baseEnd_3733309 := by
    simpa [prefixWord, tailWord_3733309, baseEnd_3733309] using wordTrace_append hprefix tailTrace_3733309
  have hstable : (prefixWord ++ tailWord_3733309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3733309).length < 2 ^ (prefixWord ++ tailWord_3733309).sum := by decide
  have hdescent : baseEnd_3733309 < baseStart_3733309 := by decide
  rcases family_descends (prefixWord ++ tailWord_3733309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3733331 : List Nat := [1, 1, 1, 2, 1, 1, 3, 1, 6, 3, 3]
def baseStart_3733331 : Nat := 118140960795 + 3733331 * 2 ^ 59
def prefixEnd_3733331 : Nat := 4983230072969 + 3 ^ 40 * 3733331 * 2
def baseEnd_3733331 : Nat := 1916993245330638058993229

theorem tailTrace_3733331 : CollatzResearch.WordTrace tailWord_3733331 prefixEnd_3733331 1916993245330638058993229 := by
  unfold tailWord_3733331
  simp only [CollatzResearch.WordTrace]
  refine ⟨136165768037786864017807847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90777178691857909345205231 136165768037786864017807847)
  ·
    refine ⟨204248652056680296026711771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136165768037786864017807847 204248652056680296026711771)
    ·
      refine ⟨306372978085020444040067657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204248652056680296026711771 306372978085020444040067657)
      ·
        refine ⟨229779733563765333030050743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 306372978085020444040067657 229779733563765333030050743)
        ·
          refine ⟨344669600345647999545076115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 229779733563765333030050743 344669600345647999545076115)
          ·
            refine ⟨517004400518471999317614173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 344669600345647999545076115 517004400518471999317614173)
            ·
              refine ⟨193876650194426999744105315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 517004400518471999317614173 193876650194426999744105315)
              ·
                refine ⟨290814975291640499616157973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 193876650194426999744105315 290814975291640499616157973)
                ·
                  refine ⟨13631951966795648419507405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 290814975291640499616157973 13631951966795648419507405)
                  ·
                    refine ⟨5111981987548368157315277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13631951966795648419507405 5111981987548368157315277)
                    ·
                      refine ⟨1916993245330638058993229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5111981987548368157315277 1916993245330638058993229)
                      ·
                        rfl

theorem cell23_3733331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 1, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 1, 6, 3, 3].length) (baseStart_3733331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3733331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3733331 prefixEnd_3733331 := by exact prefixLift 3733331
  have htrace : WordTrace (prefixWord ++ tailWord_3733331) baseStart_3733331 baseEnd_3733331 := by
    simpa [prefixWord, tailWord_3733331, baseEnd_3733331] using wordTrace_append hprefix tailTrace_3733331
  have hstable : (prefixWord ++ tailWord_3733331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3733331).length < 2 ^ (prefixWord ++ tailWord_3733331).sum := by decide
  have hdescent : baseEnd_3733331 < baseStart_3733331 := by decide
  rcases family_descends (prefixWord ++ tailWord_3733331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3733338 : List Nat := [3, 1, 1, 2, 1, 3, 2, 5, 5]
def baseStart_3733338 : Nat := 118140960795 + 3733338 * 2 ^ 59
def prefixEnd_3733338 : Nat := 4983230072969 + 3 ^ 40 * 3733338 * 2
def baseEnd_3733338 : Nat := 212999648855024392400633

theorem tailTrace_3733338 : CollatzResearch.WordTrace tailWord_3733338 prefixEnd_3733338 212999648855024392400633 := by
  unfold tailWord_3733338
  simp only [CollatzResearch.WordTrace]
  refine ⟨34041505837190376053328167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90777348899174336142208445 34041505837190376053328167)
  ·
    refine ⟨51062258755785564079992251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34041505837190376053328167 51062258755785564079992251)
    ·
      refine ⟨76593388133678346119988377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51062258755785564079992251 76593388133678346119988377)
      ·
        refine ⟨57445041100258759589991283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76593388133678346119988377 57445041100258759589991283)
        ·
          refine ⟨86167561650388139384986925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57445041100258759589991283 86167561650388139384986925)
          ·
            refine ⟨32312835618895552269370097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 86167561650388139384986925 32312835618895552269370097)
            ·
              refine ⟨24234626714171664202027573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32312835618895552269370097 24234626714171664202027573)
              ·
                refine ⟨2271996254453593518940085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24234626714171664202027573 2271996254453593518940085)
                ·
                  refine ⟨212999648855024392400633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2271996254453593518940085 212999648855024392400633)
                  ·
                    rfl

theorem cell23_3733338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 2, 5, 5].length) (baseStart_3733338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3733338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3733338 prefixEnd_3733338 := by exact prefixLift 3733338
  have htrace : WordTrace (prefixWord ++ tailWord_3733338) baseStart_3733338 baseEnd_3733338 := by
    simpa [prefixWord, tailWord_3733338, baseEnd_3733338] using wordTrace_append hprefix tailTrace_3733338
  have hstable : (prefixWord ++ tailWord_3733338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3733338).length < 2 ^ (prefixWord ++ tailWord_3733338).sum := by decide
  have hdescent : baseEnd_3733338 < baseStart_3733338 := by decide
  rcases family_descends (prefixWord ++ tailWord_3733338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3733361 : List Nat := [1, 2, 2, 2, 1, 3, 1, 3, 1, 2, 5]
def baseStart_3733361 : Nat := 118140960795 + 3733361 * 2 ^ 59
def prefixEnd_3733361 : Nat := 4983230072969 + 3 ^ 40 * 3733361 * 2
def baseEnd_3733361 : Nat := 1917008649750272941618091

theorem tailTrace_3733361 : CollatzResearch.WordTrace tailWord_3733361 prefixEnd_3733361 1917008649750272941618091 := by
  unfold tailWord_3733361
  simp only [CollatzResearch.WordTrace]
  refine ⟨136166862227678179141399937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90777908151785452760933291 136166862227678179141399937)
  ·
    refine ⟨102125146670758634356049953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136166862227678179141399937 102125146670758634356049953)
    ·
      refine ⟨76593860003068975767037465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102125146670758634356049953 76593860003068975767037465)
      ·
        refine ⟨57445395002301731825278099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76593860003068975767037465 57445395002301731825278099)
        ·
          refine ⟨86168092503452597737917149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57445395002301731825278099 86168092503452597737917149)
          ·
            refine ⟨32313034688794724151718931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 86168092503452597737917149 32313034688794724151718931)
            ·
              refine ⟨48469552033192086227578397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32313034688794724151718931 48469552033192086227578397)
              ·
                refine ⟨18176082012447032335341899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48469552033192086227578397 18176082012447032335341899)
                ·
                  refine ⟨27264123018670548503012849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18176082012447032335341899 27264123018670548503012849)
                  ·
                    refine ⟨20448092264002911377259637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27264123018670548503012849 20448092264002911377259637)
                    ·
                      refine ⟨1917008649750272941618091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20448092264002911377259637 1917008649750272941618091)
                      ·
                        rfl

theorem cell23_3733361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 3, 1, 2, 5].length) (baseStart_3733361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3733361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3733361 prefixEnd_3733361 := by exact prefixLift 3733361
  have htrace : WordTrace (prefixWord ++ tailWord_3733361) baseStart_3733361 baseEnd_3733361 := by
    simpa [prefixWord, tailWord_3733361, baseEnd_3733361] using wordTrace_append hprefix tailTrace_3733361
  have hstable : (prefixWord ++ tailWord_3733361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3733361).length < 2 ^ (prefixWord ++ tailWord_3733361).sum := by decide
  have hdescent : baseEnd_3733361 < baseStart_3733361 := by decide
  rcases family_descends (prefixWord ++ tailWord_3733361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3733371 : List Nat := [1, 1, 1, 1, 1, 5, 1, 4, 1, 3, 4]
def baseStart_3733371 : Nat := 118140960795 + 3733371 * 2 ^ 59
def prefixEnd_3733371 : Nat := 4983230072969 + 3 ^ 40 * 3733371 * 2
def baseEnd_3733371 : Nat := 1917013784556817902493045

theorem tailTrace_3733371 : CollatzResearch.WordTrace tailWord_3733371 prefixEnd_3733371 1917013784556817902493045 := by
  unfold tailWord_3733371
  simp only [CollatzResearch.WordTrace]
  refine ⟨136167226957641950849263967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90778151305094633899509311 136167226957641950849263967)
  ·
    refine ⟨204250840436462926273895951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136167226957641950849263967 204250840436462926273895951)
    ·
      refine ⟨306376260654694389410843927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204250840436462926273895951 306376260654694389410843927)
      ·
        refine ⟨459564390982041584116265891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 306376260654694389410843927 459564390982041584116265891)
        ·
          refine ⟨689346586473062376174398837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 459564390982041584116265891 689346586473062376174398837)
          ·
            refine ⟨64626242481849597766349891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 689346586473062376174398837 64626242481849597766349891)
            ·
              refine ⟨96939363722774396649524837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64626242481849597766349891 96939363722774396649524837)
              ·
                refine ⟨18176130698020199371785907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 96939363722774396649524837 18176130698020199371785907)
                ·
                  refine ⟨27264196047030299057678861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18176130698020199371785907 27264196047030299057678861)
                  ·
                    refine ⟨10224073517636362146629573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27264196047030299057678861 10224073517636362146629573)
                    ·
                      refine ⟨1917013784556817902493045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10224073517636362146629573 1917013784556817902493045)
                      ·
                        rfl

theorem cell23_3733371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 4, 1, 3, 4].length) (baseStart_3733371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3733371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3733371 prefixEnd_3733371 := by exact prefixLift 3733371
  have htrace : WordTrace (prefixWord ++ tailWord_3733371) baseStart_3733371 baseEnd_3733371 := by
    simpa [prefixWord, tailWord_3733371, baseEnd_3733371] using wordTrace_append hprefix tailTrace_3733371
  have hstable : (prefixWord ++ tailWord_3733371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3733371).length < 2 ^ (prefixWord ++ tailWord_3733371).sum := by decide
  have hdescent : baseEnd_3733371 < baseStart_3733371 := by decide
  rcases family_descends (prefixWord ++ tailWord_3733371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3733388 : List Nat := [2, 2, 1, 2, 1, 2, 1, 1, 3, 6, 2]
def baseStart_3733388 : Nat := 118140960795 + 3733388 * 2 ^ 59
def prefixEnd_3733388 : Nat := 4983230072969 + 3 ^ 40 * 3733388 * 2
def baseEnd_3733388 : Nat := 1917022513727944335980467

theorem tailTrace_3733388 : CollatzResearch.WordTrace tailWord_3733388 prefixEnd_3733388 1917022513727944335980467 := by
  unfold tailWord_3733388
  simp only [CollatzResearch.WordTrace]
  refine ⟨68083923499290181376316409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90778564665720241835088545 68083923499290181376316409)
  ·
    refine ⟨51062942624467636032237307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68083923499290181376316409 51062942624467636032237307)
    ·
      refine ⟨76594413936701454048355961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51062942624467636032237307 76594413936701454048355961)
      ·
        refine ⟨57445810452526090536266971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76594413936701454048355961 57445810452526090536266971)
        ·
          refine ⟨86168715678789135804400457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57445810452526090536266971 86168715678789135804400457)
          ·
            refine ⟨64626536759091851853300343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86168715678789135804400457 64626536759091851853300343)
            ·
              refine ⟨96939805138637777779950515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64626536759091851853300343 96939805138637777779950515)
              ·
                refine ⟨145409707707956666669925773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 96939805138637777779950515 145409707707956666669925773)
                ·
                  refine ⟨54528640390483750001222165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 145409707707956666669925773 54528640390483750001222165)
                  ·
                    refine ⟨2556030018303925781307289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 54528640390483750001222165 2556030018303925781307289)
                    ·
                      refine ⟨1917022513727944335980467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2556030018303925781307289 1917022513727944335980467)
                      ·
                        rfl

theorem cell23_3733388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 1, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 1, 3, 6, 2].length) (baseStart_3733388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3733388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3733388 prefixEnd_3733388 := by exact prefixLift 3733388
  have htrace : WordTrace (prefixWord ++ tailWord_3733388) baseStart_3733388 baseEnd_3733388 := by
    simpa [prefixWord, tailWord_3733388, baseEnd_3733388] using wordTrace_append hprefix tailTrace_3733388
  have hstable : (prefixWord ++ tailWord_3733388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3733388).length < 2 ^ (prefixWord ++ tailWord_3733388).sum := by decide
  have hdescent : baseEnd_3733388 < baseStart_3733388 := by decide
  rcases family_descends (prefixWord ++ tailWord_3733388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3733401 : List Nat := [1, 2, 1, 2, 1, 3, 3, 1, 2, 1, 6]
def baseStart_3733401 : Nat := 118140960795 + 3733401 * 2 ^ 59
def prefixEnd_3733401 : Nat := 4983230072969 + 3 ^ 40 * 3733401 * 2
def baseEnd_3733401 : Nat := 1917029188976452785117907

theorem tailTrace_3733401 : CollatzResearch.WordTrace tailWord_3733401 prefixEnd_3733401 1917029188976452785117907 := by
  unfold tailWord_3733401
  simp only [CollatzResearch.WordTrace]
  refine ⟨136168321147533265972856057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90778880765022177315237371 136168321147533265972856057)
  ·
    refine ⟨102126240860649949479642043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136168321147533265972856057 102126240860649949479642043)
    ·
      refine ⟨153189361290974924219463065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102126240860649949479642043 153189361290974924219463065)
      ·
        refine ⟨114892020968231193164597299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 153189361290974924219463065 114892020968231193164597299)
        ·
          refine ⟨172338031452346789746895949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114892020968231193164597299 172338031452346789746895949)
          ·
            refine ⟨64626761794630046155085981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 172338031452346789746895949 64626761794630046155085981)
            ·
              refine ⟨24235035672986267308157243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64626761794630046155085981 24235035672986267308157243)
              ·
                refine ⟨36352553509479400962235865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24235035672986267308157243 36352553509479400962235865)
                ·
                  refine ⟨27264415132109550721676899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36352553509479400962235865 27264415132109550721676899)
                  ·
                    refine ⟨40896622698164326082515349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27264415132109550721676899 40896622698164326082515349)
                    ·
                      refine ⟨1917029188976452785117907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 40896622698164326082515349 1917029188976452785117907)
                      ·
                        rfl

theorem cell23_3733401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 3, 1, 2, 1, 6].length) (baseStart_3733401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3733401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3733401 prefixEnd_3733401 := by exact prefixLift 3733401
  have htrace : WordTrace (prefixWord ++ tailWord_3733401) baseStart_3733401 baseEnd_3733401 := by
    simpa [prefixWord, tailWord_3733401, baseEnd_3733401] using wordTrace_append hprefix tailTrace_3733401
  have hstable : (prefixWord ++ tailWord_3733401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3733401).length < 2 ^ (prefixWord ++ tailWord_3733401).sum := by decide
  have hdescent : baseEnd_3733401 < baseStart_3733401 := by decide
  rcases family_descends (prefixWord ++ tailWord_3733401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3733405 : List Nat := [1, 4, 2, 1, 2, 2, 1, 2, 2, 4, 2]
def baseStart_3733405 : Nat := 118140960795 + 3733405 * 2 ^ 59
def prefixEnd_3733405 : Nat := 4983230072969 + 3 ^ 40 * 3733405 * 2
def baseEnd_3733405 : Nat := 1917031242899070769467889

theorem tailTrace_3733405 : CollatzResearch.WordTrace tailWord_3733405 prefixEnd_3733405 1917031242899070769467889 := by
  unfold tailWord_3733405
  simp only [CollatzResearch.WordTrace]
  refine ⟨136168467039518774656001669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90778978026345849770667779 136168467039518774656001669)
  ·
    refine ⟨25531587569909770248000313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 136168467039518774656001669 25531587569909770248000313)
    ·
      refine ⟨19148690677432327686000235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25531587569909770248000313 19148690677432327686000235)
      ·
        refine ⟨28723036016148491529000353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19148690677432327686000235 28723036016148491529000353)
        ·
          refine ⟨21542277012111368646750265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28723036016148491529000353 21542277012111368646750265)
          ·
            refine ⟨16156707759083526485062699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21542277012111368646750265 16156707759083526485062699)
            ·
              refine ⟨24235061638625289727594049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16156707759083526485062699 24235061638625289727594049)
              ·
                refine ⟨18176296228968967295695537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24235061638625289727594049 18176296228968967295695537)
                ·
                  refine ⟨13632222171726725471771653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18176296228968967295695537 13632222171726725471771653)
                  ·
                    refine ⟨2556041657198761025957185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13632222171726725471771653 2556041657198761025957185)
                    ·
                      refine ⟨1917031242899070769467889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2556041657198761025957185 1917031242899070769467889)
                      ·
                        rfl

theorem cell23_3733405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 1, 2, 2, 4, 2].length) (baseStart_3733405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3733405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3733405 prefixEnd_3733405 := by exact prefixLift 3733405
  have htrace : WordTrace (prefixWord ++ tailWord_3733405) baseStart_3733405 baseEnd_3733405 := by
    simpa [prefixWord, tailWord_3733405, baseEnd_3733405] using wordTrace_append hprefix tailTrace_3733405
  have hstable : (prefixWord ++ tailWord_3733405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3733405).length < 2 ^ (prefixWord ++ tailWord_3733405).sum := by decide
  have hdescent : baseEnd_3733405 < baseStart_3733405 := by decide
  rcases family_descends (prefixWord ++ tailWord_3733405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3733408 : List Nat := [2, 1, 1, 4, 1, 1, 1, 3, 4, 2, 3]
def baseStart_3733408 : Nat := 118140960795 + 3733408 * 2 ^ 59
def prefixEnd_3733408 : Nat := 4983230072969 + 3 ^ 40 * 3733408 * 2
def baseEnd_3733408 : Nat := 1917032783341034257730375

theorem tailTrace_3733408 : CollatzResearch.WordTrace tailWord_3733408 prefixEnd_3733408 1917032783341034257730375 := by
  unfold tailWord_3733408
  simp only [CollatzResearch.WordTrace]
  refine ⟨68084288229253953084180439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90779050972338604112240585 68084288229253953084180439)
  ·
    refine ⟨102126432343880929626270659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68084288229253953084180439 102126432343880929626270659)
    ·
      refine ⟨153189648515821394439405989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102126432343880929626270659 153189648515821394439405989)
      ·
        refine ⟨28723059096716511457388623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 153189648515821394439405989 28723059096716511457388623)
        ·
          refine ⟨43084588645074767186082935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28723059096716511457388623 43084588645074767186082935)
          ·
            refine ⟨64626882967612150779124403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43084588645074767186082935 64626882967612150779124403)
            ·
              refine ⟨96940324451418226168686605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64626882967612150779124403 96940324451418226168686605)
              ·
                refine ⟨36352621669281834813257477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 96940324451418226168686605 36352621669281834813257477)
                ·
                  refine ⟨6816116562990344027485777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36352621669281834813257477 6816116562990344027485777)
                  ·
                    refine ⟨5112087422242758020614333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6816116562990344027485777 5112087422242758020614333)
                    ·
                      refine ⟨1917032783341034257730375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5112087422242758020614333 1917032783341034257730375)
                      ·
                        rfl

theorem cell23_3733408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 3, 4, 2, 3].length) (baseStart_3733408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3733408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3733408 prefixEnd_3733408 := by exact prefixLift 3733408
  have htrace : WordTrace (prefixWord ++ tailWord_3733408) baseStart_3733408 baseEnd_3733408 := by
    simpa [prefixWord, tailWord_3733408, baseEnd_3733408] using wordTrace_append hprefix tailTrace_3733408
  have hstable : (prefixWord ++ tailWord_3733408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3733408).length < 2 ^ (prefixWord ++ tailWord_3733408).sum := by decide
  have hdescent : baseEnd_3733408 < baseStart_3733408 := by decide
  rcases family_descends (prefixWord ++ tailWord_3733408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3733415 : List Nat := [1, 1, 6, 1, 2, 1, 1, 3, 3, 4]
def baseStart_3733415 : Nat := 118140960795 + 3733415 * 2 ^ 59
def prefixEnd_3733415 : Nat := 4983230072969 + 3 ^ 40 * 3733415 * 2
def baseEnd_3733415 : Nat := 639012125901871910114281

theorem tailTrace_3733415 : CollatzResearch.WordTrace tailWord_3733415 prefixEnd_3733415 639012125901871910114281 := by
  unfold tailWord_3733415
  simp only [CollatzResearch.WordTrace]
  refine ⟨136168831769482546363865699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90779221179655030909243799 136168831769482546363865699)
  ·
    refine ⟨204253247654223819545798549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136168831769482546363865699 204253247654223819545798549)
    ·
      refine ⟨9574370983791741541209307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 204253247654223819545798549 9574370983791741541209307)
      ·
        refine ⟨14361556475687612311813961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9574370983791741541209307 14361556475687612311813961)
        ·
          refine ⟨10771167356765709233860471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14361556475687612311813961 10771167356765709233860471)
          ·
            refine ⟨16156751035148563850790707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10771167356765709233860471 16156751035148563850790707)
            ·
              refine ⟨24235126552722845776186061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16156751035148563850790707 24235126552722845776186061)
              ·
                refine ⟨9088172457271067166069773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24235126552722845776186061 9088172457271067166069773)
                ·
                  refine ⟨3408064671476650187276165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9088172457271067166069773 3408064671476650187276165)
                  ·
                    refine ⟨639012125901871910114281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3408064671476650187276165 639012125901871910114281)
                    ·
                      rfl

theorem cell23_3733415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 1, 3, 3, 4].length) (baseStart_3733415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3733415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3733415 prefixEnd_3733415 := by exact prefixLift 3733415
  have htrace : WordTrace (prefixWord ++ tailWord_3733415) baseStart_3733415 baseEnd_3733415 := by
    simpa [prefixWord, tailWord_3733415, baseEnd_3733415] using wordTrace_append hprefix tailTrace_3733415
  have hstable : (prefixWord ++ tailWord_3733415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3733415).length < 2 ^ (prefixWord ++ tailWord_3733415).sum := by decide
  have hdescent : baseEnd_3733415 < baseStart_3733415 := by decide
  rcases family_descends (prefixWord ++ tailWord_3733415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3733431 : List Nat := [1, 1, 3, 1, 3, 1, 1, 1, 3, 2, 6]
def baseStart_3733431 : Nat := 118140960795 + 3733431 * 2 ^ 59
def prefixEnd_3733431 : Nat := 4983230072969 + 3 ^ 40 * 3733431 * 2
def baseEnd_3733431 : Nat := 1917044593396087667742769

theorem tailTrace_3733431 : CollatzResearch.WordTrace tailWord_3733431 prefixEnd_3733431 1917044593396087667742769 := by
  unfold tailWord_3733431
  simp only [CollatzResearch.WordTrace]
  refine ⟨136169415337424581096448147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90779610224949720730965431 136169415337424581096448147)
  ·
    refine ⟨204254123006136871644672221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136169415337424581096448147 204254123006136871644672221)
    ·
      refine ⟨76595296127301326866752083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 204254123006136871644672221 76595296127301326866752083)
      ·
        refine ⟨114892944190951990300128125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76595296127301326866752083 114892944190951990300128125)
        ·
          refine ⟨43084854071606996362548047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 114892944190951990300128125 43084854071606996362548047)
          ·
            refine ⟨64627281107410494543822071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43084854071606996362548047 64627281107410494543822071)
            ·
              refine ⟨96940921661115741815733107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64627281107410494543822071 96940921661115741815733107)
              ·
                refine ⟨145411382491673612723599661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 96940921661115741815733107 145411382491673612723599661)
                ·
                  refine ⟨54529268434377604771349873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 145411382491673612723599661 54529268434377604771349873)
                  ·
                    refine ⟨40896951325783203578512405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 54529268434377604771349873 40896951325783203578512405)
                    ·
                      refine ⟨1917044593396087667742769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 40896951325783203578512405 1917044593396087667742769)
                      ·
                        rfl

theorem cell23_3733431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 1, 3, 2, 6].length) (baseStart_3733431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3733431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3733431 prefixEnd_3733431 := by exact prefixLift 3733431
  have htrace : WordTrace (prefixWord ++ tailWord_3733431) baseStart_3733431 baseEnd_3733431 := by
    simpa [prefixWord, tailWord_3733431, baseEnd_3733431] using wordTrace_append hprefix tailTrace_3733431
  have hstable : (prefixWord ++ tailWord_3733431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3733431).length < 2 ^ (prefixWord ++ tailWord_3733431).sum := by decide
  have hdescent : baseEnd_3733431 < baseStart_3733431 := by decide
  rcases family_descends (prefixWord ++ tailWord_3733431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3733472 : List Nat := [2, 1, 1, 3, 1, 1, 1, 8, 1, 1, 3]
def baseStart_3733472 : Nat := 118140960795 + 3733472 * 2 ^ 59
def prefixEnd_3733472 : Nat := 4983230072969 + 3 ^ 40 * 3733472 * 2
def baseEnd_3733472 : Nat := 1917065646102922007330081

theorem tailTrace_3733472 : CollatzResearch.WordTrace tailWord_3733472 prefixEnd_3733472 1917065646102922007330081 := by
  unfold tailWord_3733472
  simp only [CollatzResearch.WordTrace]
  refine ⟨68085455365138022549345335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90780607153517363399127113 68085455365138022549345335)
  ·
    refine ⟨102128183047707033824018003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68085455365138022549345335 102128183047707033824018003)
    ·
      refine ⟨153192274571560550736027005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102128183047707033824018003 153192274571560550736027005)
      ·
        refine ⟨57447102964335206526010127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 153192274571560550736027005 57447102964335206526010127)
        ·
          refine ⟨86170654446502809789015191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57447102964335206526010127 86170654446502809789015191)
          ·
            refine ⟨129255981669754214683522787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86170654446502809789015191 129255981669754214683522787)
            ·
              refine ⟨193883972504631322025284181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 129255981669754214683522787 193883972504631322025284181)
              ·
                refine ⟨2272077802788648304983799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 193883972504631322025284181 2272077802788648304983799)
                ·
                  refine ⟨3408116704182972457475699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2272077802788648304983799 3408116704182972457475699)
                  ·
                    refine ⟨5112175056274458686213549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3408116704182972457475699 5112175056274458686213549)
                    ·
                      refine ⟨1917065646102922007330081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5112175056274458686213549 1917065646102922007330081)
                      ·
                        rfl

theorem cell23_3733472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 8, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 8, 1, 1, 3].length) (baseStart_3733472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3733472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3733472 prefixEnd_3733472 := by exact prefixLift 3733472
  have htrace : WordTrace (prefixWord ++ tailWord_3733472) baseStart_3733472 baseEnd_3733472 := by
    simpa [prefixWord, tailWord_3733472, baseEnd_3733472] using wordTrace_append hprefix tailTrace_3733472
  have hstable : (prefixWord ++ tailWord_3733472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3733472).length < 2 ^ (prefixWord ++ tailWord_3733472).sum := by decide
  have hdescent : baseEnd_3733472 < baseStart_3733472 := by decide
  rcases family_descends (prefixWord ++ tailWord_3733472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3733479 : List Nat := [1, 1, 5, 2, 4, 1, 2, 1, 6]
def baseStart_3733479 : Nat := 118140960795 + 3733479 * 2 ^ 59
def prefixEnd_3733479 : Nat := 4983230072969 + 3 ^ 40 * 3733479 * 2
def baseEnd_3733479 : Nat := 213007693385278164438061

theorem tailTrace_3733479 : CollatzResearch.WordTrace tailWord_3733479 prefixEnd_3733479 213007693385278164438061 := by
  unfold tailWord_3733479
  simp only [CollatzResearch.WordTrace]
  refine ⟨136171166041250685294195491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90780777360833790196130327 136171166041250685294195491)
  ·
    refine ⟨204256749061876027941293237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136171166041250685294195491 204256749061876027941293237)
    ·
      refine ⟨19149070224550877619496241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 204256749061876027941293237 19149070224550877619496241)
      ·
        refine ⟨14361802668413158214622181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19149070224550877619496241 14361802668413158214622181)
        ·
          refine ⟨2692838000327467165241659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14361802668413158214622181 2692838000327467165241659)
          ·
            refine ⟨4039257000491200747862489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2692838000327467165241659 4039257000491200747862489)
            ·
              refine ⟨3029442750368400560896867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4039257000491200747862489 3029442750368400560896867)
              ·
                refine ⟨4544164125552600841345301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3029442750368400560896867 4544164125552600841345301)
                ·
                  refine ⟨213007693385278164438061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4544164125552600841345301 213007693385278164438061)
                  ·
                    rfl

theorem cell23_3733479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 4, 1, 2, 1, 6].length) (baseStart_3733479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3733479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3733479 prefixEnd_3733479 := by exact prefixLift 3733479
  have htrace : WordTrace (prefixWord ++ tailWord_3733479) baseStart_3733479 baseEnd_3733479 := by
    simpa [prefixWord, tailWord_3733479, baseEnd_3733479] using wordTrace_append hprefix tailTrace_3733479
  have hstable : (prefixWord ++ tailWord_3733479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3733479).length < 2 ^ (prefixWord ++ tailWord_3733479).sum := by decide
  have hdescent : baseEnd_3733479 < baseStart_3733479 := by decide
  rcases family_descends (prefixWord ++ tailWord_3733479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3733512 : List Nat := [2, 1, 3, 2, 1, 2, 5, 1, 1, 1, 4]
def baseStart_3733512 : Nat := 118140960795 + 3733512 * 2 ^ 59
def prefixEnd_3733512 : Nat := 4983230072969 + 3 ^ 40 * 3733512 * 2
def baseEnd_3733512 : Nat := 1917086185329101850829897

theorem tailTrace_3733512 : CollatzResearch.WordTrace tailWord_3733512 prefixEnd_3733512 1917086185329101850829897 := by
  unfold tailWord_3733512
  simp only [CollatzResearch.WordTrace]
  refine ⟨68086184825065565965073395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90781579766754087953431193 68086184825065565965073395)
  ·
    refine ⟨102129277237598348947610093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68086184825065565965073395 102129277237598348947610093)
    ·
      refine ⟨38298478964099380855353785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102129277237598348947610093 38298478964099380855353785)
      ·
        refine ⟨28723859223074535641515339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38298478964099380855353785 28723859223074535641515339)
        ·
          refine ⟨43085788834611803462273009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28723859223074535641515339 43085788834611803462273009)
          ·
            refine ⟨32314341625958852596704757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43085788834611803462273009 32314341625958852596704757)
            ·
              refine ⟨3029469527433642430941071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 32314341625958852596704757 3029469527433642430941071)
              ·
                refine ⟨4544204291150463646411607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3029469527433642430941071 4544204291150463646411607)
                ·
                  refine ⟨6816306436725695469617411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4544204291150463646411607 6816306436725695469617411)
                  ·
                    refine ⟨10224459655088543204426117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6816306436725695469617411 10224459655088543204426117)
                    ·
                      refine ⟨1917086185329101850829897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10224459655088543204426117 1917086185329101850829897)
                      ·
                        rfl

theorem cell23_3733512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 5, 1, 1, 1, 4].length) (baseStart_3733512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3733512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3733512 prefixEnd_3733512 := by exact prefixLift 3733512
  have htrace : WordTrace (prefixWord ++ tailWord_3733512) baseStart_3733512 baseEnd_3733512 := by
    simpa [prefixWord, tailWord_3733512, baseEnd_3733512] using wordTrace_append hprefix tailTrace_3733512
  have hstable : (prefixWord ++ tailWord_3733512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3733512).length < 2 ^ (prefixWord ++ tailWord_3733512).sum := by decide
  have hdescent : baseEnd_3733512 < baseStart_3733512 := by decide
  rcases family_descends (prefixWord ++ tailWord_3733512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3733517 : List Nat := [1, 7, 1, 2, 2, 1, 2, 2, 1, 4]
def baseStart_3733517 : Nat := 118140960795 + 3733517 * 2 ^ 59
def prefixEnd_3733517 : Nat := 4983230072969 + 3 ^ 40 * 3733517 * 2
def baseEnd_3733517 : Nat := 639029584244124777089125

theorem tailTrace_3733517 : CollatzResearch.WordTrace tailWord_3733517 prefixEnd_3733517 639029584244124777089125 := by
  unfold tailWord_3733517
  simp only [CollatzResearch.WordTrace]
  refine ⟨136172552015113017784078805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90781701343408678522719203 136172552015113017784078805)
  ·
    refine ⟨3191544187854211354314347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 136172552015113017784078805 3191544187854211354314347)
    ·
      refine ⟨4787316281781317031471521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3191544187854211354314347 4787316281781317031471521)
      ·
        refine ⟨3590487211335987773603641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4787316281781317031471521 3590487211335987773603641)
        ·
          refine ⟨2692865408501990830202731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3590487211335987773603641 2692865408501990830202731)
          ·
            refine ⟨4039298112752986245304097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2692865408501990830202731 4039298112752986245304097)
            ·
              refine ⟨3029473584564739683978073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4039298112752986245304097 3029473584564739683978073)
              ·
                refine ⟨2272105188423554762983555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3029473584564739683978073 2272105188423554762983555)
                ·
                  refine ⟨3408157782635332144475333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2272105188423554762983555 3408157782635332144475333)
                  ·
                    refine ⟨639029584244124777089125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3408157782635332144475333 639029584244124777089125)
                    ·
                      rfl

theorem cell23_3733517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 2, 1, 2, 2, 1, 4].length) (baseStart_3733517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3733517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3733517 prefixEnd_3733517 := by exact prefixLift 3733517
  have htrace : WordTrace (prefixWord ++ tailWord_3733517) baseStart_3733517 baseEnd_3733517 := by
    simpa [prefixWord, tailWord_3733517, baseEnd_3733517] using wordTrace_append hprefix tailTrace_3733517
  have hstable : (prefixWord ++ tailWord_3733517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3733517).length < 2 ^ (prefixWord ++ tailWord_3733517).sum := by decide
  have hdescent : baseEnd_3733517 < baseStart_3733517 := by decide
  rcases family_descends (prefixWord ++ tailWord_3733517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3733596 : List Nat := [2, 2, 4, 1, 1, 3, 3, 1, 2, 1, 3]
def baseStart_3733596 : Nat := 118140960795 + 3733596 * 2 ^ 59
def prefixEnd_3733596 : Nat := 4983230072969 + 3 ^ 40 * 3733596 * 2
def baseEnd_3733596 : Nat := 1917129317704079522179511

theorem tailTrace_3733596 : CollatzResearch.WordTrace tailWord_3733596 prefixEnd_3733596 1917129317704079522179511 := by
  unfold tailWord_3733596
  simp only [CollatzResearch.WordTrace]
  refine ⟨68087716690913407138102321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90783622254551209517469761 68087716690913407138102321)
  ·
    refine ⟨51065787518185055353576741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68087716690913407138102321 51065787518185055353576741)
    ·
      refine ⟨9574835159659697878795639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 51065787518185055353576741 9574835159659697878795639)
      ·
        refine ⟨14362252739489546818193459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9574835159659697878795639 14362252739489546818193459)
        ·
          refine ⟨21543379109234320227290189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14362252739489546818193459 21543379109234320227290189)
          ·
            refine ⟨8078767165962870085233821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21543379109234320227290189 8078767165962870085233821)
            ·
              refine ⟨3029537687236076281962683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8078767165962870085233821 3029537687236076281962683)
              ·
                refine ⟨4544306530854114422944025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3029537687236076281962683 4544306530854114422944025)
                ·
                  refine ⟨3408229898140585817208019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4544306530854114422944025 3408229898140585817208019)
                  ·
                    refine ⟨5112344847210878725812029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3408229898140585817208019 5112344847210878725812029)
                    ·
                      refine ⟨1917129317704079522179511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5112344847210878725812029 1917129317704079522179511)
                      ·
                        rfl

theorem cell23_3733596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 3, 1, 2, 1, 3].length) (baseStart_3733596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3733596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3733596 prefixEnd_3733596 := by exact prefixLift 3733596
  have htrace : WordTrace (prefixWord ++ tailWord_3733596) baseStart_3733596 baseEnd_3733596 := by
    simpa [prefixWord, tailWord_3733596, baseEnd_3733596] using wordTrace_append hprefix tailTrace_3733596
  have hstable : (prefixWord ++ tailWord_3733596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3733596).length < 2 ^ (prefixWord ++ tailWord_3733596).sum := by decide
  have hdescent : baseEnd_3733596 < baseStart_3733596 := by decide
  rcases family_descends (prefixWord ++ tailWord_3733596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3733622 : List Nat := [5, 1, 1, 2, 1, 3, 1, 1, 2, 1, 5]
def baseStart_3733622 : Nat := 118140960795 + 3733622 * 2 ^ 59
def prefixEnd_3733622 : Nat := 4983230072969 + 3 ^ 40 * 3733622 * 2
def baseEnd_3733622 : Nat := 1917142668201096420454391

theorem tailTrace_3733622 : CollatzResearch.WordTrace tailWord_3733622 prefixEnd_3733622 1917142668201096420454391 := by
  unfold tailWord_3733622
  simp only [CollatzResearch.WordTrace]
  refine ⟨8511023854983288794790695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 90784254453155080477767413 8511023854983288794790695)
  ·
    refine ⟨12766535782474933192186043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8511023854983288794790695 12766535782474933192186043)
    ·
      refine ⟨19149803673712399788279065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12766535782474933192186043 19149803673712399788279065)
      ·
        refine ⟨14362352755284299841209299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19149803673712399788279065 14362352755284299841209299)
        ·
          refine ⟨21543529132926449761813949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14362352755284299841209299 21543529132926449761813949)
          ·
            refine ⟨8078823424847418660680231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21543529132926449761813949 8078823424847418660680231)
            ·
              refine ⟨12118235137271127991020347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8078823424847418660680231 12118235137271127991020347)
              ·
                refine ⟨18177352705906691986530521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12118235137271127991020347 18177352705906691986530521)
                ·
                  refine ⟨13633014529430018989897891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18177352705906691986530521 13633014529430018989897891)
                  ·
                    refine ⟨20449521794145028484846837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13633014529430018989897891 20449521794145028484846837)
                    ·
                      refine ⟨1917142668201096420454391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20449521794145028484846837 1917142668201096420454391)
                      ·
                        rfl

theorem cell23_3733622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 1, 1, 2, 1, 5].length) (baseStart_3733622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3733622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3733622 prefixEnd_3733622 := by exact prefixLift 3733622
  have htrace : WordTrace (prefixWord ++ tailWord_3733622) baseStart_3733622 baseEnd_3733622 := by
    simpa [prefixWord, tailWord_3733622, baseEnd_3733622] using wordTrace_append hprefix tailTrace_3733622
  have hstable : (prefixWord ++ tailWord_3733622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3733622).length < 2 ^ (prefixWord ++ tailWord_3733622).sum := by decide
  have hdescent : baseEnd_3733622 < baseStart_3733622 := by decide
  rcases family_descends (prefixWord ++ tailWord_3733622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3733642 : List Nat := [3, 1, 2, 3, 1, 4, 1, 1, 7]
def baseStart_3733642 : Nat := 118140960795 + 3733642 * 2 ^ 59
def prefixEnd_3733642 : Nat := 4983230072969 + 3 ^ 40 * 3733642 * 2
def baseEnd_3733642 : Nat := 213016993090465149133811

theorem tailTrace_3733642 : CollatzResearch.WordTrace tailWord_3733642 prefixEnd_3733642 213016993090465149133811 := by
  unfold tailWord_3733642
  simp only [CollatzResearch.WordTrace]
  refine ⟨34044277784915041033094795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90784740759773442754919453 34044277784915041033094795)
  ·
    refine ⟨51066416677372561549642193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34044277784915041033094795 51066416677372561549642193)
    ·
      refine ⟨38299812508029421162231645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51066416677372561549642193 38299812508029421162231645)
      ·
        refine ⟨14362429690511032935836867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38299812508029421162231645 14362429690511032935836867)
        ·
          refine ⟨21543644535766549403755301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14362429690511032935836867 21543644535766549403755301)
          ·
            refine ⟨4039433350456228013204119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21543644535766549403755301 4039433350456228013204119)
            ·
              refine ⟨6059150025684342019806179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4039433350456228013204119 6059150025684342019806179)
              ·
                refine ⟨9088725038526513029709269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6059150025684342019806179 9088725038526513029709269)
                ·
                  refine ⟨213016993090465149133811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9088725038526513029709269 213016993090465149133811)
                  ·
                    rfl

theorem cell23_3733642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 4, 1, 1, 7].length) (baseStart_3733642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3733642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3733642 prefixEnd_3733642 := by exact prefixLift 3733642
  have htrace : WordTrace (prefixWord ++ tailWord_3733642) baseStart_3733642 baseEnd_3733642 := by
    simpa [prefixWord, tailWord_3733642, baseEnd_3733642] using wordTrace_append hprefix tailTrace_3733642
  have hstable : (prefixWord ++ tailWord_3733642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3733642).length < 2 ^ (prefixWord ++ tailWord_3733642).sum := by decide
  have hdescent : baseEnd_3733642 < baseStart_3733642 := by decide
  rcases family_descends (prefixWord ++ tailWord_3733642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3733695 : List Nat := [1, 1, 2, 2, 2, 2, 1, 2, 3, 4, 3]
def baseStart_3733695 : Nat := 118140960795 + 3733695 * 2 ^ 59
def prefixEnd_3733695 : Nat := 4983230072969 + 3 ^ 40 * 3733695 * 2
def baseEnd_3733695 : Nat := 1917180152288874634841555

theorem tailTrace_3733695 : CollatzResearch.WordTrace tailWord_3733695 prefixEnd_3733695 1917180152288874634841555 := by
  unfold tailWord_3733695
  simp only [CollatzResearch.WordTrace]
  refine ⟨136179044208468154184058539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90786029472312102789372359 136179044208468154184058539)
  ·
    refine ⟨204268566312702231276087809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136179044208468154184058539 204268566312702231276087809)
    ·
      refine ⟨153201424734526673457065857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 204268566312702231276087809 153201424734526673457065857)
      ·
        refine ⟨114901068550895005092799393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 153201424734526673457065857 114901068550895005092799393)
        ·
          refine ⟨86175801413171253819599545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114901068550895005092799393 86175801413171253819599545)
          ·
            refine ⟨64631851059878440364699659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86175801413171253819599545 64631851059878440364699659)
            ·
              refine ⟨96947776589817660547049489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64631851059878440364699659 96947776589817660547049489)
              ·
                refine ⟨72710832442363245410287117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 96947776589817660547049489 72710832442363245410287117)
                ·
                  refine ⟨27266562165886217028857669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 72710832442363245410287117 27266562165886217028857669)
                  ·
                    refine ⟨5112480406103665692910813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27266562165886217028857669 5112480406103665692910813)
                    ·
                      refine ⟨1917180152288874634841555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5112480406103665692910813 1917180152288874634841555)
                      ·
                        rfl

theorem cell23_3733695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 2, 3, 4, 3].length) (baseStart_3733695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3733695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3733695 prefixEnd_3733695 := by exact prefixLift 3733695
  have htrace : WordTrace (prefixWord ++ tailWord_3733695) baseStart_3733695 baseEnd_3733695 := by
    simpa [prefixWord, tailWord_3733695, baseEnd_3733695] using wordTrace_append hprefix tailTrace_3733695
  have hstable : (prefixWord ++ tailWord_3733695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3733695).length < 2 ^ (prefixWord ++ tailWord_3733695).sum := by decide
  have hdescent : baseEnd_3733695 < baseStart_3733695 := by decide
  rcases family_descends (prefixWord ++ tailWord_3733695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3733736 : List Nat := [2, 1, 4, 1, 2, 3, 2, 3, 1, 4]
def baseStart_3733736 : Nat := 118140960795 + 3733736 * 2 ^ 59
def prefixEnd_3733736 : Nat := 4983230072969 + 3 ^ 40 * 3733736 * 2
def baseEnd_3733736 : Nat := 639067068331902991476289

theorem tailTrace_3733736 : CollatzResearch.WordTrace tailWord_3733736 prefixEnd_3733736 639067068331902991476289 := by
  unfold tailWord_3733736
  simp only [CollatzResearch.WordTrace]
  refine ⟨68090269800659809093150531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90787026400879745457534041 68090269800659809093150531)
  ·
    refine ⟨102135404700989713639725797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68090269800659809093150531 102135404700989713639725797)
    ·
      refine ⟨19150388381435571307448587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 102135404700989713639725797 19150388381435571307448587)
      ·
        refine ⟨28725582572153356961172881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19150388381435571307448587 28725582572153356961172881)
        ·
          refine ⟨21544186929115017720879661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28725582572153356961172881 21544186929115017720879661)
          ·
            refine ⟨8079070098418131645329873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21544186929115017720879661 8079070098418131645329873)
            ·
              refine ⟨6059302573813598733997405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8079070098418131645329873 6059302573813598733997405)
              ·
                refine ⟨2272238465180099525249027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6059302573813598733997405 2272238465180099525249027)
                ·
                  refine ⟨3408357697770149287873541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2272238465180099525249027 3408357697770149287873541)
                  ·
                    refine ⟨639067068331902991476289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3408357697770149287873541 639067068331902991476289)
                    ·
                      rfl

theorem cell23_3733736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 2, 3, 1, 4].length) (baseStart_3733736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3733736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3733736 prefixEnd_3733736 := by exact prefixLift 3733736
  have htrace : WordTrace (prefixWord ++ tailWord_3733736) baseStart_3733736 baseEnd_3733736 := by
    simpa [prefixWord, tailWord_3733736, baseEnd_3733736] using wordTrace_append hprefix tailTrace_3733736
  have hstable : (prefixWord ++ tailWord_3733736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3733736).length < 2 ^ (prefixWord ++ tailWord_3733736).sum := by decide
  have hdescent : baseEnd_3733736 < baseStart_3733736 := by decide
  rcases family_descends (prefixWord ++ tailWord_3733736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3733759 : List Nat := [1, 1, 2, 2, 1, 4, 4, 1, 3, 1, 3]
def baseStart_3733759 : Nat := 118140960795 + 3733759 * 2 ^ 59
def prefixEnd_3733759 : Nat := 4983230072969 + 3 ^ 40 * 3733759 * 2
def baseEnd_3733759 : Nat := 1917213015050762384441261

theorem tailTrace_3733759 : CollatzResearch.WordTrace tailWord_3733759 prefixEnd_3733759 1917213015050762384441261 := by
  unfold tailWord_3733759
  simp only [CollatzResearch.WordTrace]
  refine ⟨136181378480236293114388331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90787585653490862076258887 136181378480236293114388331)
  ·
    refine ⟨204272067720354439671582497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136181378480236293114388331 204272067720354439671582497)
    ·
      refine ⟨153204050790265829753686873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 204272067720354439671582497 153204050790265829753686873)
      ·
        refine ⟨114903038092699372315265155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 153204050790265829753686873 114903038092699372315265155)
        ·
          refine ⟨172354557139049058472897733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114903038092699372315265155 172354557139049058472897733)
          ·
            refine ⟨32316479463571698463668325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 172354557139049058472897733 32316479463571698463668325)
            ·
              refine ⟨6059339899419693461937811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32316479463571698463668325 6059339899419693461937811)
              ·
                refine ⟨9089009849129540192906717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6059339899419693461937811 9089009849129540192906717)
                ·
                  refine ⟨3408378693423577572340019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9089009849129540192906717 3408378693423577572340019)
                  ·
                    refine ⟨5112568040135366358510029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3408378693423577572340019 5112568040135366358510029)
                    ·
                      refine ⟨1917213015050762384441261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5112568040135366358510029 1917213015050762384441261)
                      ·
                        rfl

theorem cell23_3733759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 4, 1, 3, 1, 3].length) (baseStart_3733759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3733759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3733759 prefixEnd_3733759 := by exact prefixLift 3733759
  have htrace : WordTrace (prefixWord ++ tailWord_3733759) baseStart_3733759 baseEnd_3733759 := by
    simpa [prefixWord, tailWord_3733759, baseEnd_3733759] using wordTrace_append hprefix tailTrace_3733759
  have hstable : (prefixWord ++ tailWord_3733759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3733759).length < 2 ^ (prefixWord ++ tailWord_3733759).sum := by decide
  have hdescent : baseEnd_3733759 < baseStart_3733759 := by decide
  rcases family_descends (prefixWord ++ tailWord_3733759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3733765 : List Nat := [1, 3, 1, 1, 2, 1, 2, 1, 2, 5, 4]
def baseStart_3733765 : Nat := 118140960795 + 3733765 * 2 ^ 59
def prefixEnd_3733765 : Nat := 4983230072969 + 3 ^ 40 * 3733765 * 2
def baseEnd_3733765 : Nat := 1917216095934689360966233

theorem tailTrace_3733765 : CollatzResearch.WordTrace tailWord_3733765 prefixEnd_3733765 1917216095934689360966233 := by
  unfold tailWord_3733765
  simp only [CollatzResearch.WordTrace]
  refine ⟨136181597318214556139106749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90787731545476370759404499 136181597318214556139106749)
  ·
    refine ⟨51068098994330458552165031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 136181597318214556139106749 51068098994330458552165031)
    ·
      refine ⟨76602148491495687828247547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51068098994330458552165031 76602148491495687828247547)
      ·
        refine ⟨114903222737243531742371321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76602148491495687828247547 114903222737243531742371321)
        ·
          refine ⟨86177417052932648806778491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114903222737243531742371321 86177417052932648806778491)
          ·
            refine ⟨129266125579398973210167737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86177417052932648806778491 129266125579398973210167737)
            ·
              refine ⟨96949594184549229907625803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 129266125579398973210167737 96949594184549229907625803)
              ·
                refine ⟨145424391276823844861438705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 96949594184549229907625803 145424391276823844861438705)
                ·
                  refine ⟨109068293457617883646079029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 145424391276823844861438705 109068293457617883646079029)
                  ·
                    refine ⟨10225152511651676591819909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 109068293457617883646079029 10225152511651676591819909)
                    ·
                      refine ⟨1917216095934689360966233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10225152511651676591819909 1917216095934689360966233)
                      ·
                        rfl

theorem cell23_3733765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 1, 2, 5, 4].length) (baseStart_3733765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3733765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3733765 prefixEnd_3733765 := by exact prefixLift 3733765
  have htrace : WordTrace (prefixWord ++ tailWord_3733765) baseStart_3733765 baseEnd_3733765 := by
    simpa [prefixWord, tailWord_3733765, baseEnd_3733765] using wordTrace_append hprefix tailTrace_3733765
  have hstable : (prefixWord ++ tailWord_3733765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3733765).length < 2 ^ (prefixWord ++ tailWord_3733765).sum := by decide
  have hdescent : baseEnd_3733765 < baseStart_3733765 := by decide
  rcases family_descends (prefixWord ++ tailWord_3733765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3733810 : List Nat := [3, 2, 1, 1, 5, 1, 3, 2, 1, 1, 3]
def baseStart_3733810 : Nat := 118140960795 + 3733810 * 2 ^ 59
def prefixEnd_3733810 : Nat := 4983230072969 + 3 ^ 40 * 3733810 * 2
def baseEnd_3733810 : Nat := 1917239202564141684903527

theorem tailTrace_3733810 : CollatzResearch.WordTrace tailWord_3733810 prefixEnd_3733810 1917239202564141684903527 := by
  unfold tailWord_3733810
  simp only [CollatzResearch.WordTrace]
  refine ⟨34045809650762882206123721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90788825735367685882996589 34045809650762882206123721)
  ·
    refine ⟨25534357238072161654592791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34045809650762882206123721 25534357238072161654592791)
    ·
      refine ⟨38301535857108242481889187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25534357238072161654592791 38301535857108242481889187)
      ·
        refine ⟨57452303785662363722833781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38301535857108242481889187 57452303785662363722833781)
        ·
          refine ⟨5386153479905846599015667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 57452303785662363722833781 5386153479905846599015667)
          ·
            refine ⟨8079230219858769898523501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5386153479905846599015667 8079230219858769898523501)
            ·
              refine ⟨3029711332447038711946313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8079230219858769898523501 3029711332447038711946313)
              ·
                refine ⟨2272283499335279033959735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3029711332447038711946313 2272283499335279033959735)
                ·
                  refine ⟨3408425249002918550939603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2272283499335279033959735 3408425249002918550939603)
                  ·
                    refine ⟨5112637873504377826409405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3408425249002918550939603 5112637873504377826409405)
                    ·
                      refine ⟨1917239202564141684903527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5112637873504377826409405 1917239202564141684903527)
                      ·
                        rfl

theorem cell23_3733810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 3, 2, 1, 1, 3].length) (baseStart_3733810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3733810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3733810 prefixEnd_3733810 := by exact prefixLift 3733810
  have htrace : WordTrace (prefixWord ++ tailWord_3733810) baseStart_3733810 baseEnd_3733810 := by
    simpa [prefixWord, tailWord_3733810, baseEnd_3733810] using wordTrace_append hprefix tailTrace_3733810
  have hstable : (prefixWord ++ tailWord_3733810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3733810).length < 2 ^ (prefixWord ++ tailWord_3733810).sum := by decide
  have hdescent : baseEnd_3733810 < baseStart_3733810 := by decide
  rcases family_descends (prefixWord ++ tailWord_3733810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3733816 : List Nat := [2, 1, 2, 1, 3, 1, 5, 1, 3, 2, 2]
def baseStart_3733816 : Nat := 118140960795 + 3733816 * 2 ^ 59
def prefixEnd_3733816 : Nat := 4983230072969 + 3 ^ 40 * 3733816 * 2
def baseEnd_3733816 : Nat := 1917242283448068661428499

theorem tailTrace_3733816 : CollatzResearch.WordTrace tailWord_3733816 prefixEnd_3733816 1917242283448068661428499 := by
  unfold tailWord_3733816
  simp only [CollatzResearch.WordTrace]
  refine ⟨68091728720514895924606651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90788971627353194566142201 68091728720514895924606651)
  ·
    refine ⟨102137593080772343886909977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68091728720514895924606651 102137593080772343886909977)
    ·
      refine ⟨76603194810579257915182483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102137593080772343886909977 76603194810579257915182483)
      ·
        refine ⟨114904792215868886872773725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76603194810579257915182483 114904792215868886872773725)
        ·
          refine ⟨43089297080950832577290147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 114904792215868886872773725 43089297080950832577290147)
          ·
            refine ⟨64633945621426248865935221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43089297080950832577290147 64633945621426248865935221)
            ·
              refine ⟨6059432402008710831181427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 64633945621426248865935221 6059432402008710831181427)
              ·
                refine ⟨9089148603013066246772141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6059432402008710831181427 9089148603013066246772141)
                ·
                  refine ⟨3408430726129899842539553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9089148603013066246772141 3408430726129899842539553)
                  ·
                    refine ⟨2556323044597424881904665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3408430726129899842539553 2556323044597424881904665)
                    ·
                      refine ⟨1917242283448068661428499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2556323044597424881904665 1917242283448068661428499)
                      ·
                        rfl

theorem cell23_3733816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 5, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 5, 1, 3, 2, 2].length) (baseStart_3733816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3733816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3733816 prefixEnd_3733816 := by exact prefixLift 3733816
  have htrace : WordTrace (prefixWord ++ tailWord_3733816) baseStart_3733816 baseEnd_3733816 := by
    simpa [prefixWord, tailWord_3733816, baseEnd_3733816] using wordTrace_append hprefix tailTrace_3733816
  have hstable : (prefixWord ++ tailWord_3733816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3733816).length < 2 ^ (prefixWord ++ tailWord_3733816).sum := by decide
  have hdescent : baseEnd_3733816 < baseStart_3733816 := by decide
  rcases family_descends (prefixWord ++ tailWord_3733816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3733822 : List Nat := [4, 2, 1, 2, 1, 2, 1, 10]
def baseStart_3733822 : Nat := 118140960795 + 3733822 * 2 ^ 59
def prefixEnd_3733822 : Nat := 4983230072969 + 3 ^ 40 * 3733822 * 2
def baseEnd_3733822 : Nat := 71009087567851690294573

theorem tailTrace_3733822 : CollatzResearch.WordTrace tailWord_3733822 prefixEnd_3733822 71009087567851690294573 := by
  unfold tailWord_3733822
  simp only [CollatzResearch.WordTrace]
  refine ⟨17022959534876006859241465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 90789117519338703249287813 17022959534876006859241465)
  ·
    refine ⟨12767219651157005144431099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17022959534876006859241465 12767219651157005144431099)
    ·
      refine ⟨19150829476735507716646649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12767219651157005144431099 19150829476735507716646649)
      ·
        refine ⟨14363122107551630787484987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19150829476735507716646649 14363122107551630787484987)
        ·
          refine ⟨21544683161327446181227481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14363122107551630787484987 21544683161327446181227481)
          ·
            refine ⟨16158512370995584635920611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21544683161327446181227481 16158512370995584635920611)
            ·
              refine ⟨24237768556493376953880917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16158512370995584635920611 24237768556493376953880917)
              ·
                refine ⟨71009087567851690294573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 24237768556493376953880917 71009087567851690294573)
                ·
                  rfl

theorem cell23_3733822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 1, 10].length) (baseStart_3733822 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3733822 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3733822 prefixEnd_3733822 := by exact prefixLift 3733822
  have htrace : WordTrace (prefixWord ++ tailWord_3733822) baseStart_3733822 baseEnd_3733822 := by
    simpa [prefixWord, tailWord_3733822, baseEnd_3733822] using wordTrace_append hprefix tailTrace_3733822
  have hstable : (prefixWord ++ tailWord_3733822).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3733822).length < 2 ^ (prefixWord ++ tailWord_3733822).sum := by decide
  have hdescent : baseEnd_3733822 < baseStart_3733822 := by decide
  rcases family_descends (prefixWord ++ tailWord_3733822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3733835 : List Nat := [1, 1, 1, 1, 3, 1, 1, 3, 4, 7]
def baseStart_3733835 : Nat := 118140960795 + 3733835 * 2 ^ 59
def prefixEnd_3733835 : Nat := 4983230072969 + 3 ^ 40 * 3733835 * 2
def baseEnd_3733835 : Nat := 639084013193501362363637

theorem tailTrace_3733835 : CollatzResearch.WordTrace tailWord_3733835 prefixEnd_3733835 639084013193501362363637 := by
  unfold tailWord_3733835
  simp only [CollatzResearch.WordTrace]
  refine ⟨136184150427960958094154959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90789433618640638729436639 136184150427960958094154959)
  ·
    refine ⟨204276225641941437141232439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136184150427960958094154959 204276225641941437141232439)
    ·
      refine ⟨306414338462912155711848659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204276225641941437141232439 306414338462912155711848659)
      ·
        refine ⟨459621507694368233567772989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 306414338462912155711848659 459621507694368233567772989)
        ·
          refine ⟨172358065385388087587914871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 459621507694368233567772989 172358065385388087587914871)
          ·
            refine ⟨258537098078082131381872307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 172358065385388087587914871 258537098078082131381872307)
            ·
              refine ⟨387805647117123197072808461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 258537098078082131381872307 387805647117123197072808461)
              ·
                refine ⟨145427117668921198902303173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 387805647117123197072808461 145427117668921198902303173)
                ·
                  refine ⟨27267584562922724794181845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 145427117668921198902303173 27267584562922724794181845)
                  ·
                    refine ⟨639084013193501362363637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 27267584562922724794181845 639084013193501362363637)
                    ·
                      rfl

theorem cell23_3733835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 3, 4, 7].length) (baseStart_3733835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3733835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3733835 prefixEnd_3733835 := by exact prefixLift 3733835
  have htrace : WordTrace (prefixWord ++ tailWord_3733835) baseStart_3733835 baseEnd_3733835 := by
    simpa [prefixWord, tailWord_3733835, baseEnd_3733835] using wordTrace_append hprefix tailTrace_3733835
  have hstable : (prefixWord ++ tailWord_3733835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3733835).length < 2 ^ (prefixWord ++ tailWord_3733835).sum := by decide
  have hdescent : baseEnd_3733835 < baseStart_3733835 := by decide
  rcases family_descends (prefixWord ++ tailWord_3733835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3733872 : List Nat := [2, 1, 1, 1, 4, 3, 1, 1, 2, 3, 4]
def baseStart_3733872 : Nat := 118140960795 + 3733872 * 2 ^ 59
def prefixEnd_3733872 : Nat := 4983230072969 + 3 ^ 40 * 3733872 * 2
def baseEnd_3733872 : Nat := 1917271038364720442328241

theorem tailTrace_3733872 : CollatzResearch.WordTrace tailWord_3733872 prefixEnd_3733872 1917271038364720442328241 := by
  unfold tailWord_3733872
  simp only [CollatzResearch.WordTrace]
  refine ⟨68092749964413456706625935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90790333285884608942167913 68092749964413456706625935)
  ·
    refine ⟨102139124946620185059938903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68092749964413456706625935 102139124946620185059938903)
    ·
      refine ⟨153208687419930277589908355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102139124946620185059938903 153208687419930277589908355)
      ·
        refine ⟨229813031129895416384862533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153208687419930277589908355 229813031129895416384862533)
        ·
          refine ⟨43089943336855390572161725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 229813031129895416384862533 43089943336855390572161725)
          ·
            refine ⟨16158728751320771464560647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43089943336855390572161725 16158728751320771464560647)
            ·
              refine ⟨24238093126981157196840971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16158728751320771464560647 24238093126981157196840971)
              ·
                refine ⟨36357139690471735795261457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24238093126981157196840971 36357139690471735795261457)
                ·
                  refine ⟨27267854767853801846446093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36357139690471735795261457 27267854767853801846446093)
                  ·
                    refine ⟨10225445537945175692417285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27267854767853801846446093 10225445537945175692417285)
                    ·
                      refine ⟨1917271038364720442328241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10225445537945175692417285 1917271038364720442328241)
                      ·
                        rfl

theorem cell23_3733872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 1, 1, 2, 3, 4].length) (baseStart_3733872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3733872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3733872 prefixEnd_3733872 := by exact prefixLift 3733872
  have htrace : WordTrace (prefixWord ++ tailWord_3733872) baseStart_3733872 baseEnd_3733872 := by
    simpa [prefixWord, tailWord_3733872, baseEnd_3733872] using wordTrace_append hprefix tailTrace_3733872
  have hstable : (prefixWord ++ tailWord_3733872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3733872).length < 2 ^ (prefixWord ++ tailWord_3733872).sum := by decide
  have hdescent : baseEnd_3733872 < baseStart_3733872 := by decide
  rcases family_descends (prefixWord ++ tailWord_3733872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3733923 : List Nat := [1, 1, 1, 4, 1, 4, 3, 2, 2, 2, 2]
def baseStart_3733923 : Nat := 118140960795 + 3733923 * 2 ^ 59
def prefixEnd_3733923 : Nat := 4983230072969 + 3 ^ 40 * 3733923 * 2
def baseEnd_3733923 : Nat := 1917297225878099742790507

theorem tailTrace_3733923 : CollatzResearch.WordTrace tailWord_3733923 prefixEnd_3733923 1917297225878099742790507 := by
  unfold tailWord_3733923
  simp only [CollatzResearch.WordTrace]
  refine ⟨136187360051642149123358423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90791573367761432748905615 136187360051642149123358423)
  ·
    refine ⟨204281040077463223685037635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136187360051642149123358423 204281040077463223685037635)
    ·
      refine ⟨306421560116194835527556453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204281040077463223685037635 306421560116194835527556453)
      ·
        refine ⟨57454042521786531661416835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 306421560116194835527556453 57454042521786531661416835)
        ·
          refine ⟨86181063782679797492125253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57454042521786531661416835 86181063782679797492125253)
          ·
            refine ⟨16158949459252462029773485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 86181063782679797492125253 16158949459252462029773485)
            ·
              refine ⟨6059606047219673261165057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16158949459252462029773485 6059606047219673261165057)
              ·
                refine ⟨4544704535414754945873793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6059606047219673261165057 4544704535414754945873793)
                ·
                  refine ⟨3408528401561066209405345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4544704535414754945873793 3408528401561066209405345)
                  ·
                    refine ⟨2556396301170799657054009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3408528401561066209405345 2556396301170799657054009)
                    ·
                      refine ⟨1917297225878099742790507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2556396301170799657054009 1917297225878099742790507)
                      ·
                        rfl

theorem cell23_3733923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 3, 2, 2, 2, 2].length) (baseStart_3733923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3733923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3733923 prefixEnd_3733923 := by exact prefixLift 3733923
  have htrace : WordTrace (prefixWord ++ tailWord_3733923) baseStart_3733923 baseEnd_3733923 := by
    simpa [prefixWord, tailWord_3733923, baseEnd_3733923] using wordTrace_append hprefix tailTrace_3733923
  have hstable : (prefixWord ++ tailWord_3733923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3733923).length < 2 ^ (prefixWord ++ tailWord_3733923).sum := by decide
  have hdescent : baseEnd_3733923 < baseStart_3733923 := by decide
  rcases family_descends (prefixWord ++ tailWord_3733923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3733952 : List Nat := [2, 1, 1, 2, 3, 1, 1, 2, 3, 2, 5]
def baseStart_3733952 : Nat := 118140960795 + 3733952 * 2 ^ 59
def prefixEnd_3733952 : Nat := 4983230072969 + 3 ^ 40 * 3733952 * 2
def baseEnd_3733952 : Nat := 1917312116817080129327873

theorem tailTrace_3733952 : CollatzResearch.WordTrace tailWord_3733952 prefixEnd_3733952 1917312116817080129327873 := by
  unfold tailWord_3733952
  simp only [CollatzResearch.WordTrace]
  refine ⟨68094208884268543538082055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90792278512358058050776073 68094208884268543538082055)
  ·
    refine ⟨102141313326402815307123083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68094208884268543538082055 102141313326402815307123083)
    ·
      refine ⟨153211969989604222960684625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102141313326402815307123083 153211969989604222960684625)
      ·
        refine ⟨114908977492203167220513469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 153211969989604222960684625 114908977492203167220513469)
        ·
          refine ⟨43090866559576187707692551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 114908977492203167220513469 43090866559576187707692551)
          ·
            refine ⟨64636299839364281561538827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43090866559576187707692551 64636299839364281561538827)
            ·
              refine ⟨96954449759046422342308241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64636299839364281561538827 96954449759046422342308241)
              ·
                refine ⟨72715837319284816756731181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 96954449759046422342308241 72715837319284816756731181)
                ·
                  refine ⟨27268438994731806283774193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 72715837319284816756731181 27268438994731806283774193)
                  ·
                    refine ⟨20451329246048854712830645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27268438994731806283774193 20451329246048854712830645)
                    ·
                      refine ⟨1917312116817080129327873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20451329246048854712830645 1917312116817080129327873)
                      ·
                        rfl

theorem cell23_3733952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 2, 3, 2, 5].length) (baseStart_3733952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3733952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3733952 prefixEnd_3733952 := by exact prefixLift 3733952
  have htrace : WordTrace (prefixWord ++ tailWord_3733952) baseStart_3733952 baseEnd_3733952 := by
    simpa [prefixWord, tailWord_3733952, baseEnd_3733952] using wordTrace_append hprefix tailTrace_3733952
  have hstable : (prefixWord ++ tailWord_3733952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3733952).length < 2 ^ (prefixWord ++ tailWord_3733952).sum := by decide
  have hdescent : baseEnd_3733952 < baseStart_3733952 := by decide
  rcases family_descends (prefixWord ++ tailWord_3733952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3733999 : List Nat := [1, 1, 2, 1, 4, 1, 1, 1, 6, 2, 3]
def baseStart_3733999 : Nat := 118140960795 + 3733999 * 2 ^ 59
def prefixEnd_3733999 : Nat := 4983230072969 + 3 ^ 40 * 3733999 * 2
def baseEnd_3733999 : Nat := 1917336250407841445440157

theorem tailTrace_3733999 : CollatzResearch.WordTrace tailWord_3733999 prefixEnd_3733999 1917336250407841445440157 := by
  unfold tailWord_3733999
  simp only [CollatzResearch.WordTrace]
  refine ⟨136190131999366814103125051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90793421332911209402083367 136190131999366814103125051)
  ·
    refine ⟨204285197999050221154687577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136190131999366814103125051 204285197999050221154687577)
    ·
      refine ⟨153213898499287665866015683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 204285197999050221154687577 153213898499287665866015683)
      ·
        refine ⟨229820847748931498799023525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153213898499287665866015683 229820847748931498799023525)
        ·
          refine ⟨43091408952924656024816911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 229820847748931498799023525 43091408952924656024816911)
          ·
            refine ⟨64637113429386984037225367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43091408952924656024816911 64637113429386984037225367)
            ·
              refine ⟨96955670144080476055838051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64637113429386984037225367 96955670144080476055838051)
              ·
                refine ⟨145433505216120714083757077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 96955670144080476055838051 145433505216120714083757077)
                ·
                  refine ⟨6817195557005658472676113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 145433505216120714083757077 6817195557005658472676113)
                  ·
                    refine ⟨5112896667754243854507085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6817195557005658472676113 5112896667754243854507085)
                    ·
                      refine ⟨1917336250407841445440157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5112896667754243854507085 1917336250407841445440157)
                      ·
                        rfl

theorem cell23_3733999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 1, 6, 2, 3].length) (baseStart_3733999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3733999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3733999 prefixEnd_3733999 := by exact prefixLift 3733999
  have htrace : WordTrace (prefixWord ++ tailWord_3733999) baseStart_3733999 baseEnd_3733999 := by
    simpa [prefixWord, tailWord_3733999, baseEnd_3733999] using wordTrace_append hprefix tailTrace_3733999
  have hstable : (prefixWord ++ tailWord_3733999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3733999).length < 2 ^ (prefixWord ++ tailWord_3733999).sum := by decide
  have hdescent : baseEnd_3733999 < baseStart_3733999 := by decide
  rcases family_descends (prefixWord ++ tailWord_3733999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3734006 : List Nat := [5, 1, 1, 1, 2, 1, 2, 1, 5, 4]
def baseStart_3734006 : Nat := 118140960795 + 3734006 * 2 ^ 59
def prefixEnd_3734006 : Nat := 4983230072969 + 3 ^ 40 * 3734006 * 2
def baseEnd_3734006 : Nat := 639113281590807639350875

theorem tailTrace_3734006 : CollatzResearch.WordTrace tailWord_3734006 prefixEnd_3734006 639113281590807639350875 := by
  unfold tailWord_3734006
  simp only [CollatzResearch.WordTrace]
  refine ⟨8511899206896340893664367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 90793591540227636199086581 8511899206896340893664367)
  ·
    refine ⟨12767848810344511340496551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8511899206896340893664367 12767848810344511340496551)
    ·
      refine ⟨19151773215516767010744827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12767848810344511340496551 19151773215516767010744827)
      ·
        refine ⟨28727659823275150516117241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19151773215516767010744827 28727659823275150516117241)
        ·
          refine ⟨21545744867456362887087931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28727659823275150516117241 21545744867456362887087931)
          ·
            refine ⟨32318617301184544330631897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21545744867456362887087931 32318617301184544330631897)
            ·
              refine ⟨24238962975888408247973923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32318617301184544330631897 24238962975888408247973923)
              ·
                refine ⟨36358444463832612371960885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24238962975888408247973923 36358444463832612371960885)
                ·
                  refine ⟨3408604168484307409871333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 36358444463832612371960885 3408604168484307409871333)
                  ·
                    refine ⟨639113281590807639350875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3408604168484307409871333 639113281590807639350875)
                    ·
                      rfl

theorem cell23_3734006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 2, 1, 5, 4].length) (baseStart_3734006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3734006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3734006 prefixEnd_3734006 := by exact prefixLift 3734006
  have htrace : WordTrace (prefixWord ++ tailWord_3734006) baseStart_3734006 baseEnd_3734006 := by
    simpa [prefixWord, tailWord_3734006, baseEnd_3734006] using wordTrace_append hprefix tailTrace_3734006
  have hstable : (prefixWord ++ tailWord_3734006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3734006).length < 2 ^ (prefixWord ++ tailWord_3734006).sum := by decide
  have hdescent : baseEnd_3734006 < baseStart_3734006 := by decide
  rcases family_descends (prefixWord ++ tailWord_3734006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3734032 : List Nat := [2, 1, 1, 1, 1, 1, 1, 2, 4, 9]
def baseStart_3734032 : Nat := 118140960795 + 3734032 * 2 ^ 59
def prefixEnd_3734032 : Nat := 4983230072969 + 3 ^ 40 * 3734032 * 2
def baseEnd_3734032 : Nat := 639117731756479938775835

theorem tailTrace_3734032 : CollatzResearch.WordTrace tailWord_3734032 prefixEnd_3734032 639117731756479938775835 := by
  unfold tailWord_3734032
  simp only [CollatzResearch.WordTrace]
  refine ⟨68095667804123630369538175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90794223738831507159384233 68095667804123630369538175)
  ·
    refine ⟨102143501706185445554307263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68095667804123630369538175 102143501706185445554307263)
    ·
      refine ⟨153215252559278168331460895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102143501706185445554307263 153215252559278168331460895)
      ·
        refine ⟨229822878838917252497191343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153215252559278168331460895 229822878838917252497191343)
        ·
          refine ⟨344734318258375878745787015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 229822878838917252497191343 344734318258375878745787015)
          ·
            refine ⟨517101477387563818118680523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 344734318258375878745787015 517101477387563818118680523)
            ·
              refine ⟨775652216081345727178020785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 517101477387563818118680523 775652216081345727178020785)
              ·
                refine ⟨581739162061009295383515589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 775652216081345727178020785 581739162061009295383515589)
                ·
                  refine ⟨109076092886439242884409173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 581739162061009295383515589 109076092886439242884409173)
                  ·
                    refine ⟨639117731756479938775835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 109076092886439242884409173 639117731756479938775835)
                    ·
                      rfl

theorem cell23_3734032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 4, 9].length) (baseStart_3734032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3734032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3734032 prefixEnd_3734032 := by exact prefixLift 3734032
  have htrace : WordTrace (prefixWord ++ tailWord_3734032) baseStart_3734032 baseEnd_3734032 := by
    simpa [prefixWord, tailWord_3734032, baseEnd_3734032] using wordTrace_append hprefix tailTrace_3734032
  have hstable : (prefixWord ++ tailWord_3734032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3734032).length < 2 ^ (prefixWord ++ tailWord_3734032).sum := by decide
  have hdescent : baseEnd_3734032 < baseStart_3734032 := by decide
  rcases family_descends (prefixWord ++ tailWord_3734032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3734040 : List Nat := [2, 1, 2, 3, 3, 1, 4, 2, 1, 4]
def baseStart_3734040 : Nat := 118140960795 + 3734040 * 2 ^ 59
def prefixEnd_3734040 : Nat := 4983230072969 + 3 ^ 40 * 3734040 * 2
def baseEnd_3734040 : Nat := 639119101038225261675823

theorem tailTrace_3734040 : CollatzResearch.WordTrace tailWord_3734040 prefixEnd_3734040 639119101038225261675823 := by
  unfold tailWord_3734040
  simp only [CollatzResearch.WordTrace]
  refine ⟨68095813696109139052683787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90794418261478852070245049 68095813696109139052683787)
  ·
    refine ⟨102143720544163708579025681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68095813696109139052683787 102143720544163708579025681)
    ·
      refine ⟨76607790408122781434269261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102143720544163708579025681 76607790408122781434269261)
      ·
        refine ⟨28727921403046043037850973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76607790408122781434269261 28727921403046043037850973)
        ·
          refine ⟨10772970526142266139194115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28727921403046043037850973 10772970526142266139194115)
          ·
            refine ⟨16159455789213399208791173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10772970526142266139194115 16159455789213399208791173)
            ·
              refine ⟨3029897960477512351648345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16159455789213399208791173 3029897960477512351648345)
              ·
                refine ⟨2272423470358134263736259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3029897960477512351648345 2272423470358134263736259)
                ·
                  refine ⟨3408635205537201395604389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2272423470358134263736259 3408635205537201395604389)
                  ·
                    refine ⟨639119101038225261675823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3408635205537201395604389 639119101038225261675823)
                    ·
                      rfl

theorem cell23_3734040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 4, 2, 1, 4].length) (baseStart_3734040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3734040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3734040 prefixEnd_3734040 := by exact prefixLift 3734040
  have htrace : WordTrace (prefixWord ++ tailWord_3734040) baseStart_3734040 baseEnd_3734040 := by
    simpa [prefixWord, tailWord_3734040, baseEnd_3734040] using wordTrace_append hprefix tailTrace_3734040
  have hstable : (prefixWord ++ tailWord_3734040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3734040).length < 2 ^ (prefixWord ++ tailWord_3734040).sum := by decide
  have hdescent : baseEnd_3734040 < baseStart_3734040 := by decide
  rcases family_descends (prefixWord ++ tailWord_3734040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3734049 : List Nat := [1, 2, 3, 2, 2, 1, 1, 1, 5, 5]
def baseStart_3734049 : Nat := 118140960795 + 3734049 * 2 ^ 59
def prefixEnd_3734049 : Nat := 4983230072969 + 3 ^ 40 * 3734049 * 2
def baseEnd_3734049 : Nat := 639120641480188749938309

theorem tailTrace_3734049 : CollatzResearch.WordTrace tailWord_3734049 prefixEnd_3734049 639120641480188749938309 := by
  unfold tailWord_3734049
  simp only [CollatzResearch.WordTrace]
  refine ⟨136191955649185672642445201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90794637099457115094963467 136191955649185672642445201)
  ·
    refine ⟨102143966736889254481833901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136191955649185672642445201 102143966736889254481833901)
    ·
      refine ⟨38303987526333470430687713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102143966736889254481833901 38303987526333470430687713)
      ·
        refine ⟨28727990644750102823015785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38303987526333470430687713 28727990644750102823015785)
        ·
          refine ⟨21545992983562577117261839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28727990644750102823015785 21545992983562577117261839)
          ·
            refine ⟨32318989475343865675892759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21545992983562577117261839 32318989475343865675892759)
            ·
              refine ⟨48478484213015798513839139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32318989475343865675892759 48478484213015798513839139)
              ·
                refine ⟨72717726319523697770758709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48478484213015798513839139 72717726319523697770758709)
                ·
                  refine ⟨6817286842455346666008629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 72717726319523697770758709 6817286842455346666008629)
                  ·
                    refine ⟨639120641480188749938309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6817286842455346666008629 639120641480188749938309)
                    ·
                      rfl

theorem cell23_3734049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 1, 5, 5].length) (baseStart_3734049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3734049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3734049 prefixEnd_3734049 := by exact prefixLift 3734049
  have htrace : WordTrace (prefixWord ++ tailWord_3734049) baseStart_3734049 baseEnd_3734049 := by
    simpa [prefixWord, tailWord_3734049, baseEnd_3734049] using wordTrace_append hprefix tailTrace_3734049
  have hstable : (prefixWord ++ tailWord_3734049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3734049).length < 2 ^ (prefixWord ++ tailWord_3734049).sum := by decide
  have hdescent : baseEnd_3734049 < baseStart_3734049 := by decide
  rcases family_descends (prefixWord ++ tailWord_3734049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3734079 : List Nat := [1, 1, 2, 2, 3, 2, 1, 4, 1, 6]
def baseStart_3734079 : Nat := 118140960795 + 3734079 * 2 ^ 59
def prefixEnd_3734079 : Nat := 4983230072969 + 3 ^ 40 * 3734079 * 2
def baseEnd_3734079 : Nat := 639125776286733710813263

theorem tailTrace_3734079 : CollatzResearch.WordTrace tailWord_3734079 prefixEnd_3734079 639125776286733710813263 := by
  unfold tailWord_3734079
  simp only [CollatzResearch.WordTrace]
  refine ⟨136193049839076987766037291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90795366559384658510691527 136193049839076987766037291)
  ·
    refine ⟨204289574758615481649055937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136193049839076987766037291 204289574758615481649055937)
    ·
      refine ⟨153217181068961611236791953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 204289574758615481649055937 153217181068961611236791953)
      ·
        refine ⟨114912885801721208427593965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 153217181068961611236791953 114912885801721208427593965)
        ·
          refine ⟨43092332175645453160347737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 114912885801721208427593965 43092332175645453160347737)
          ·
            refine ⟨32319249131734089870260803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43092332175645453160347737 32319249131734089870260803)
            ·
              refine ⟨48478873697601134805391205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32319249131734089870260803 48478873697601134805391205)
              ·
                refine ⟨9089788818300212776010851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48478873697601134805391205 9089788818300212776010851)
                ·
                  refine ⟨13634683227450319164016277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9089788818300212776010851 13634683227450319164016277)
                  ·
                    refine ⟨639125776286733710813263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13634683227450319164016277 639125776286733710813263)
                    ·
                      rfl

theorem cell23_3734079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 4, 1, 6].length) (baseStart_3734079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3734079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3734079 prefixEnd_3734079 := by exact prefixLift 3734079
  have htrace : WordTrace (prefixWord ++ tailWord_3734079) baseStart_3734079 baseEnd_3734079 := by
    simpa [prefixWord, tailWord_3734079, baseEnd_3734079] using wordTrace_append hprefix tailTrace_3734079
  have hstable : (prefixWord ++ tailWord_3734079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3734079).length < 2 ^ (prefixWord ++ tailWord_3734079).sum := by decide
  have hdescent : baseEnd_3734079 < baseStart_3734079 := by decide
  rcases family_descends (prefixWord ++ tailWord_3734079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3734096 : List Nat := [2, 1, 1, 1, 1, 3, 2, 6, 2, 4]
def baseStart_3734096 : Nat := 118140960795 + 3734096 * 2 ^ 59
def prefixEnd_3734096 : Nat := 4983230072969 + 3 ^ 40 * 3734096 * 2
def baseEnd_3734096 : Nat := 639128686010442521975737

theorem tailTrace_3734096 : CollatzResearch.WordTrace tailWord_3734096 prefixEnd_3734096 639128686010442521975737 := by
  unfold tailWord_3734096
  simp only [CollatzResearch.WordTrace]
  refine ⟨68096834940007699834703071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90795779920010266446270761 68096834940007699834703071)
  ·
    refine ⟨102145252410011549752054607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68096834940007699834703071 102145252410011549752054607)
    ·
      refine ⟨153217878615017324628081911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102145252410011549752054607 153217878615017324628081911)
      ·
        refine ⟨229826817922525986942122867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153217878615017324628081911 229826817922525986942122867)
        ·
          refine ⟨344740226883788980413184301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 229826817922525986942122867 344740226883788980413184301)
          ·
            refine ⟨129277585081420867654944113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 344740226883788980413184301 129277585081420867654944113)
            ·
              refine ⟨96958188811065650741208085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 129277585081420867654944113 96958188811065650741208085)
              ·
                refine ⟨4544915100518702378494129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 96958188811065650741208085 4544915100518702378494129)
                ·
                  refine ⟨3408686325389026783870597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4544915100518702378494129 3408686325389026783870597)
                  ·
                    refine ⟨639128686010442521975737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3408686325389026783870597 639128686010442521975737)
                    ·
                      rfl

theorem cell23_3734096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 6, 2, 4].length) (baseStart_3734096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3734096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3734096 prefixEnd_3734096 := by exact prefixLift 3734096
  have htrace : WordTrace (prefixWord ++ tailWord_3734096) baseStart_3734096 baseEnd_3734096 := by
    simpa [prefixWord, tailWord_3734096, baseEnd_3734096] using wordTrace_append hprefix tailTrace_3734096
  have hstable : (prefixWord ++ tailWord_3734096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3734096).length < 2 ^ (prefixWord ++ tailWord_3734096).sum := by decide
  have hdescent : baseEnd_3734096 < baseStart_3734096 := by decide
  rcases family_descends (prefixWord ++ tailWord_3734096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3734120 : List Nat := [2, 1, 4, 3, 2, 1, 2, 2, 1, 1, 4]
def baseStart_3734120 : Nat := 118140960795 + 3734120 * 2 ^ 59
def prefixEnd_3734120 : Nat := 4983230072969 + 3 ^ 40 * 3734120 * 2
def baseEnd_3734120 : Nat := 1917398381567035472027101

theorem tailTrace_3734120 : CollatzResearch.WordTrace tailWord_3734120 prefixEnd_3734120 1917398381567035472027101 := by
  unfold tailWord_3734120
  simp only [CollatzResearch.WordTrace]
  refine ⟨68097272615964225884139907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90796363487952301178853209 68097272615964225884139907)
  ·
    refine ⟨102145908923946338826209861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68097272615964225884139907 102145908923946338826209861)
    ·
      refine ⟨19152357923239938529914349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 102145908923946338826209861 19152357923239938529914349)
      ·
        refine ⟨7182134221214976948717881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19152357923239938529914349 7182134221214976948717881)
        ·
          refine ⟨5386600665911232711538411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7182134221214976948717881 5386600665911232711538411)
          ·
            refine ⟨8079900998866849067307617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5386600665911232711538411 8079900998866849067307617)
            ·
              refine ⟨6059925749150136800480713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8079900998866849067307617 6059925749150136800480713)
              ·
                refine ⟨4544944311862602600360535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6059925749150136800480713 4544944311862602600360535)
                ·
                  refine ⟨6817416467793903900540803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4544944311862602600360535 6817416467793903900540803)
                  ·
                    refine ⟨10226124701690855850811205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6817416467793903900540803 10226124701690855850811205)
                    ·
                      refine ⟨1917398381567035472027101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10226124701690855850811205 1917398381567035472027101)
                      ·
                        rfl

theorem cell23_3734120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 2, 2, 1, 1, 4].length) (baseStart_3734120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3734120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3734120 prefixEnd_3734120 := by exact prefixLift 3734120
  have htrace : WordTrace (prefixWord ++ tailWord_3734120) baseStart_3734120 baseEnd_3734120 := by
    simpa [prefixWord, tailWord_3734120, baseEnd_3734120] using wordTrace_append hprefix tailTrace_3734120
  have hstable : (prefixWord ++ tailWord_3734120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3734120).length < 2 ^ (prefixWord ++ tailWord_3734120).sum := by decide
  have hdescent : baseEnd_3734120 < baseStart_3734120 := by decide
  rcases family_descends (prefixWord ++ tailWord_3734120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3734126 : List Nat := [4, 1, 2, 2, 2, 2, 1, 9]
def baseStart_3734126 : Nat := 118140960795 + 3734126 * 2 ^ 59
def prefixEnd_3734126 : Nat := 4983230072969 + 3 ^ 40 * 3734126 * 2
def baseEnd_3734126 : Nat := 71014868979665275872299

theorem tailTrace_3734126 : CollatzResearch.WordTrace tailWord_3734126 prefixEnd_3734126 71014868979665275872299 := by
  unfold tailWord_3734126
  simp only [CollatzResearch.WordTrace]
  refine ⟨17024345508738339349124779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 90796509379937809861998821 17024345508738339349124779)
  ·
    refine ⟨25536518263107509023687169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17024345508738339349124779 25536518263107509023687169)
    ·
      refine ⟨19152388697330631767765377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25536518263107509023687169 19152388697330631767765377)
      ·
        refine ⟨14364291522997973825824033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19152388697330631767765377 14364291522997973825824033)
        ·
          refine ⟨10773218642248480369368025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14364291522997973825824033 10773218642248480369368025)
          ·
            refine ⟨8079913981686360277026019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10773218642248480369368025 8079913981686360277026019)
            ·
              refine ⟨12119870972529540415539029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8079913981686360277026019 12119870972529540415539029)
              ·
                refine ⟨71014868979665275872299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 12119870972529540415539029 71014868979665275872299)
                ·
                  rfl

theorem cell23_3734126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 1, 9].length) (baseStart_3734126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3734126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3734126 prefixEnd_3734126 := by exact prefixLift 3734126
  have htrace : WordTrace (prefixWord ++ tailWord_3734126) baseStart_3734126 baseEnd_3734126 := by
    simpa [prefixWord, tailWord_3734126, baseEnd_3734126] using wordTrace_append hprefix tailTrace_3734126
  have hstable : (prefixWord ++ tailWord_3734126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3734126).length < 2 ^ (prefixWord ++ tailWord_3734126).sum := by decide
  have hdescent : baseEnd_3734126 < baseStart_3734126 := by decide
  rcases family_descends (prefixWord ++ tailWord_3734126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3734137 : List Nat := [1, 2, 1, 3, 3, 2, 3, 3, 1, 2, 2]
def baseStart_3734137 : Nat := 118140960795 + 3734137 * 2 ^ 59
def prefixEnd_3734137 : Nat := 4983230072969 + 3 ^ 40 * 3734137 * 2
def baseEnd_3734137 : Nat := 1917407110738161905514523

theorem tailTrace_3734137 : CollatzResearch.WordTrace tailWord_3734137 prefixEnd_3734137 1917407110738161905514523 := by
  unfold tailWord_3734137
  simp only [CollatzResearch.WordTrace]
  refine ⟨136195165272866863671648665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90796776848577909114432443 136195165272866863671648665)
  ·
    refine ⟨102146373954650147753736499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136195165272866863671648665 102146373954650147753736499)
    ·
      refine ⟨153219560931975221630604749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102146373954650147753736499 153219560931975221630604749)
      ·
        refine ⟨57457335349490708111476781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 153219560931975221630604749 57457335349490708111476781)
        ·
          refine ⟨21546500756059015541803793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57457335349490708111476781 21546500756059015541803793)
          ·
            refine ⟨16159875567044261656352845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21546500756059015541803793 16159875567044261656352845)
            ·
              refine ⟨6059953337641598121132317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16159875567044261656352845 6059953337641598121132317)
              ·
                refine ⟨2272482501615599295424619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6059953337641598121132317 2272482501615599295424619)
                ·
                  refine ⟨3408723752423398943136929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2272482501615599295424619 3408723752423398943136929)
                  ·
                    refine ⟨2556542814317549207352697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3408723752423398943136929 2556542814317549207352697)
                    ·
                      refine ⟨1917407110738161905514523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2556542814317549207352697 1917407110738161905514523)
                      ·
                        rfl

theorem cell23_3734137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 3, 3, 1, 2, 2].length) (baseStart_3734137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3734137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3734137 prefixEnd_3734137 := by exact prefixLift 3734137
  have htrace : WordTrace (prefixWord ++ tailWord_3734137) baseStart_3734137 baseEnd_3734137 := by
    simpa [prefixWord, tailWord_3734137, baseEnd_3734137] using wordTrace_append hprefix tailTrace_3734137
  have hstable : (prefixWord ++ tailWord_3734137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3734137).length < 2 ^ (prefixWord ++ tailWord_3734137).sum := by decide
  have hdescent : baseEnd_3734137 < baseStart_3734137 := by decide
  rcases family_descends (prefixWord ++ tailWord_3734137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3734153 : List Nat := [1, 2, 1, 1, 4, 1, 1, 6, 2, 1, 3]
def baseStart_3734153 : Nat := 118140960795 + 3734153 * 2 ^ 59
def prefixEnd_3734153 : Nat := 4983230072969 + 3 ^ 40 * 3734153 * 2
def baseEnd_3734153 : Nat := 1917415326428633842914449

theorem tailTrace_3734153 : CollatzResearch.WordTrace tailWord_3734153 prefixEnd_3734153 1917415326428633842914449 := by
  unfold tailWord_3734153
  simp only [CollatzResearch.WordTrace]
  refine ⟨136195748840808898404231113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90797165893872598936154075 136195748840808898404231113)
  ·
    refine ⟨102146811630606673803173335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136195748840808898404231113 102146811630606673803173335)
    ·
      refine ⟨153220217445910010704760003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102146811630606673803173335 153220217445910010704760003)
      ·
        refine ⟨229830326168865016057140005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153220217445910010704760003 229830326168865016057140005)
        ·
          refine ⟨43093186156662190510713751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 229830326168865016057140005 43093186156662190510713751)
          ·
            refine ⟨64639779234993285766070627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43093186156662190510713751 64639779234993285766070627)
            ·
              refine ⟨96959668852489928649105941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64639779234993285766070627 96959668852489928649105941)
              ·
                refine ⟨4544984477460465405426841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 96959668852489928649105941 4544984477460465405426841)
                ·
                  refine ⟨3408738358095349054070131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4544984477460465405426841 3408738358095349054070131)
                  ·
                    refine ⟨5113107537143023581105197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3408738358095349054070131 5113107537143023581105197)
                    ·
                      refine ⟨1917415326428633842914449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5113107537143023581105197 1917415326428633842914449)
                      ·
                        rfl

theorem cell23_3734153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 6, 2, 1, 3].length) (baseStart_3734153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3734153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3734153 prefixEnd_3734153 := by exact prefixLift 3734153
  have htrace : WordTrace (prefixWord ++ tailWord_3734153) baseStart_3734153 baseEnd_3734153 := by
    simpa [prefixWord, tailWord_3734153, baseEnd_3734153] using wordTrace_append hprefix tailTrace_3734153
  have hstable : (prefixWord ++ tailWord_3734153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3734153).length < 2 ^ (prefixWord ++ tailWord_3734153).sum := by decide
  have hdescent : baseEnd_3734153 < baseStart_3734153 := by decide
  rcases family_descends (prefixWord ++ tailWord_3734153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3734154 : List Nat := [3, 1, 2, 3, 4, 1, 1, 1, 3, 2, 2]
def baseStart_3734154 : Nat := 118140960795 + 3734154 * 2 ^ 59
def prefixEnd_3734154 : Nat := 4983230072969 + 3 ^ 40 * 3734154 * 2
def baseEnd_3734154 : Nat := 1917415839909288339001945

theorem tailTrace_3734154 : CollatzResearch.WordTrace tailWord_3734154 prefixEnd_3734154 1917415839909288339001945 := by
  unfold tailWord_3734154
  simp only [CollatzResearch.WordTrace]
  refine ⟨34048946328451318893754379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90797190209203517050011677 34048946328451318893754379)
  ·
    refine ⟨51073419492676978340631569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34048946328451318893754379 51073419492676978340631569)
    ·
      refine ⟨38305064619507733755473677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51073419492676978340631569 38305064619507733755473677)
      ·
        refine ⟨14364399232315400158302629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38305064619507733755473677 14364399232315400158302629)
        ·
          refine ⟨2693324856059137529681743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14364399232315400158302629 2693324856059137529681743)
          ·
            refine ⟨4039987284088706294522615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2693324856059137529681743 4039987284088706294522615)
            ·
              refine ⟨6059980926133059441783923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4039987284088706294522615 6059980926133059441783923)
              ·
                refine ⟨9089971389199589162675885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6059980926133059441783923 9089971389199589162675885)
                ·
                  refine ⟨3408739270949845936003457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9089971389199589162675885 3408739270949845936003457)
                  ·
                    refine ⟨2556554453212384452002593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3408739270949845936003457 2556554453212384452002593)
                    ·
                      refine ⟨1917415839909288339001945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2556554453212384452002593 1917415839909288339001945)
                      ·
                        rfl

theorem cell23_3734154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 4, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 4, 1, 1, 1, 3, 2, 2].length) (baseStart_3734154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3734154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3734154 prefixEnd_3734154 := by exact prefixLift 3734154
  have htrace : WordTrace (prefixWord ++ tailWord_3734154) baseStart_3734154 baseEnd_3734154 := by
    simpa [prefixWord, tailWord_3734154, baseEnd_3734154] using wordTrace_append hprefix tailTrace_3734154
  have hstable : (prefixWord ++ tailWord_3734154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3734154).length < 2 ^ (prefixWord ++ tailWord_3734154).sum := by decide
  have hdescent : baseEnd_3734154 < baseStart_3734154 := by decide
  rcases family_descends (prefixWord ++ tailWord_3734154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3734159 : List Nat := [1, 1, 2, 1, 1, 1, 1, 5, 1, 5, 4]
def baseStart_3734159 : Nat := 118140960795 + 3734159 * 2 ^ 59
def prefixEnd_3734159 : Nat := 4983230072969 + 3 ^ 40 * 3734159 * 2
def baseEnd_3734159 : Nat := 1917418407312560819439421

theorem tailTrace_3734159 : CollatzResearch.WordTrace tailWord_3734159 prefixEnd_3734159 1917418407312560819439421 := by
  unfold tailWord_3734159
  simp only [CollatzResearch.WordTrace]
  refine ⟨136195967678787161428949531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90797311785858107619299687 136195967678787161428949531)
  ·
    refine ⟨204293951518180742143424297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136195967678787161428949531 204293951518180742143424297)
    ·
      refine ⟨153220463638635556607568223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 204293951518180742143424297 153220463638635556607568223)
      ·
        refine ⟨229830695457953334911352335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153220463638635556607568223 229830695457953334911352335)
        ·
          refine ⟨344746043186930002367028503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 229830695457953334911352335 344746043186930002367028503)
          ·
            refine ⟨517119064780395003550542755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 344746043186930002367028503 517119064780395003550542755)
            ·
              refine ⟨775678597170592505325814133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 517119064780395003550542755 775678597170592505325814133)
              ·
                refine ⟨72719868484743047374295075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 775678597170592505325814133 72719868484743047374295075)
                ·
                  refine ⟨109079802727114571061442613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 72719868484743047374295075 109079802727114571061442613)
                  ·
                    refine ⟨10226231505666991037010245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 109079802727114571061442613 10226231505666991037010245)
                    ·
                      refine ⟨1917418407312560819439421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10226231505666991037010245 1917418407312560819439421)
                      ·
                        rfl

theorem cell23_3734159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 5, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 5, 1, 5, 4].length) (baseStart_3734159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3734159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3734159 prefixEnd_3734159 := by exact prefixLift 3734159
  have htrace : WordTrace (prefixWord ++ tailWord_3734159) baseStart_3734159 baseEnd_3734159 := by
    simpa [prefixWord, tailWord_3734159, baseEnd_3734159] using wordTrace_append hprefix tailTrace_3734159
  have hstable : (prefixWord ++ tailWord_3734159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3734159).length < 2 ^ (prefixWord ++ tailWord_3734159).sum := by decide
  have hdescent : baseEnd_3734159 < baseStart_3734159 := by decide
  rcases family_descends (prefixWord ++ tailWord_3734159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3734169 : List Nat := [1, 2, 1, 2, 1, 2, 4, 1, 1, 8]
def baseStart_3734169 : Nat := 118140960795 + 3734169 * 2 ^ 59
def prefixEnd_3734169 : Nat := 4983230072969 + 3 ^ 40 * 3734169 * 2
def baseEnd_3734169 : Nat := 639141180706368593438125

theorem tailTrace_3734169 : CollatzResearch.WordTrace tailWord_3734169 prefixEnd_3734169 639141180706368593438125 := by
  unfold tailWord_3734169
  simp only [CollatzResearch.WordTrace]
  refine ⟨136196332408750933136813561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90797554939167288757875707 136196332408750933136813561)
  ·
    refine ⟨102147249306563199852610171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136196332408750933136813561 102147249306563199852610171)
    ·
      refine ⟨153220873959844799778915257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102147249306563199852610171 153220873959844799778915257)
      ·
        refine ⟨114915655469883599834186443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 153220873959844799778915257 114915655469883599834186443)
        ·
          refine ⟨172373483204825399751279665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114915655469883599834186443 172373483204825399751279665)
          ·
            refine ⟨129280112403619049813459749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 172373483204825399751279665 129280112403619049813459749)
            ·
              refine ⟨24240021075678571840023703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 129280112403619049813459749 24240021075678571840023703)
              ·
                refine ⟨36360031613517857760035555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24240021075678571840023703 36360031613517857760035555)
                ·
                  refine ⟨54540047420276786640053333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36360031613517857760035555 54540047420276786640053333)
                  ·
                    refine ⟨639141180706368593438125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 54540047420276786640053333 639141180706368593438125)
                    ·
                      rfl

theorem cell23_3734169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 4, 1, 1, 8].length) (baseStart_3734169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3734169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3734169 prefixEnd_3734169 := by exact prefixLift 3734169
  have htrace : WordTrace (prefixWord ++ tailWord_3734169) baseStart_3734169 baseEnd_3734169 := by
    simpa [prefixWord, tailWord_3734169, baseEnd_3734169] using wordTrace_append hprefix tailTrace_3734169
  have hstable : (prefixWord ++ tailWord_3734169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3734169).length < 2 ^ (prefixWord ++ tailWord_3734169).sum := by decide
  have hdescent : baseEnd_3734169 < baseStart_3734169 := by decide
  rcases family_descends (prefixWord ++ tailWord_3734169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3734219 : List Nat := [1, 1, 1, 1, 3, 2, 1, 1, 1, 3, 8]
def baseStart_3734219 : Nat := 118140960795 + 3734219 * 2 ^ 59
def prefixEnd_3734219 : Nat := 4983230072969 + 3 ^ 40 * 3734219 * 2
def baseEnd_3734219 : Nat := 1917449216151830584689145

theorem tailTrace_3734219 : CollatzResearch.WordTrace tailWord_3734219 prefixEnd_3734219 1917449216151830584689145 := by
  unfold tailWord_3734219
  simp only [CollatzResearch.WordTrace]
  refine ⟨136198156058569791676133711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90798770705713194450755807 136198156058569791676133711)
  ·
    refine ⟨204297234087854687514200567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136198156058569791676133711 204297234087854687514200567)
    ·
      refine ⟨306445851131782031271300851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204297234087854687514200567 306445851131782031271300851)
      ·
        refine ⟨459668776697673046906951277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 306445851131782031271300851 459668776697673046906951277)
        ·
          refine ⟨172375791261627392590106729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 459668776697673046906951277 172375791261627392590106729)
          ·
            refine ⟨129281843446220544442580047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 172375791261627392590106729 129281843446220544442580047)
            ·
              refine ⟨193922765169330816663870071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 129281843446220544442580047 193922765169330816663870071)
              ·
                refine ⟨290884147753996224995805107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 193922765169330816663870071 290884147753996224995805107)
                ·
                  refine ⟨436326221630994337493707661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 290884147753996224995805107 436326221630994337493707661)
                  ·
                    refine ⟨163622333111622876560140373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 436326221630994337493707661 163622333111622876560140373)
                    ·
                      refine ⟨1917449216151830584689145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 163622333111622876560140373 1917449216151830584689145)
                      ·
                        rfl

theorem cell23_3734219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 1, 1, 3, 8].length) (baseStart_3734219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3734219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3734219 prefixEnd_3734219 := by exact prefixLift 3734219
  have htrace : WordTrace (prefixWord ++ tailWord_3734219) baseStart_3734219 baseEnd_3734219 := by
    simpa [prefixWord, tailWord_3734219, baseEnd_3734219] using wordTrace_append hprefix tailTrace_3734219
  have hstable : (prefixWord ++ tailWord_3734219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3734219).length < 2 ^ (prefixWord ++ tailWord_3734219).sum := by decide
  have hdescent : baseEnd_3734219 < baseStart_3734219 := by decide
  rcases family_descends (prefixWord ++ tailWord_3734219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3734261 : List Nat := [1, 3, 6, 1, 1, 1, 1, 1, 4, 2, 2]
def baseStart_3734261 : Nat := 118140960795 + 3734261 * 2 ^ 59
def prefixEnd_3734261 : Nat := 4983230072969 + 3 ^ 40 * 3734261 * 2
def baseEnd_3734261 : Nat := 1917470782339319420363953

theorem tailTrace_3734261 : CollatzResearch.WordTrace tailWord_3734261 prefixEnd_3734261 1917470782339319420363953 := by
  unfold tailWord_3734261
  simp only [CollatzResearch.WordTrace]
  refine ⟨136199687924417632849162637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90799791949611755232775091 136199687924417632849162637)
  ·
    refine ⟨51074882971656612318435989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 136199687924417632849162637 51074882971656612318435989)
    ·
      refine ⟨2394135139296403702426687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 51074882971656612318435989 2394135139296403702426687)
      ·
        refine ⟨3591202708944605553640031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2394135139296403702426687 3591202708944605553640031)
        ·
          refine ⟨5386804063416908330460047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3591202708944605553640031 5386804063416908330460047)
          ·
            refine ⟨8080206095125362495690071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5386804063416908330460047 8080206095125362495690071)
            ·
              refine ⟨12120309142688043743535107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8080206095125362495690071 12120309142688043743535107)
              ·
                refine ⟨18180463714032065615302661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12120309142688043743535107 18180463714032065615302661)
                ·
                  refine ⟨3408836946381012302869249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18180463714032065615302661 3408836946381012302869249)
                  ·
                    refine ⟨2556627709785759227151937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3408836946381012302869249 2556627709785759227151937)
                    ·
                      refine ⟨1917470782339319420363953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2556627709785759227151937 1917470782339319420363953)
                      ·
                        rfl

theorem cell23_3734261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 1, 1, 4, 2, 2].length) (baseStart_3734261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3734261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3734261 prefixEnd_3734261 := by exact prefixLift 3734261
  have htrace : WordTrace (prefixWord ++ tailWord_3734261) baseStart_3734261 baseEnd_3734261 := by
    simpa [prefixWord, tailWord_3734261, baseEnd_3734261] using wordTrace_append hprefix tailTrace_3734261
  have hstable : (prefixWord ++ tailWord_3734261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3734261).length < 2 ^ (prefixWord ++ tailWord_3734261).sum := by decide
  have hdescent : baseEnd_3734261 < baseStart_3734261 := by decide
  rcases family_descends (prefixWord ++ tailWord_3734261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3734293 : List Nat := [1, 3, 2, 1, 2, 2, 1, 4, 3, 4]
def baseStart_3734293 : Nat := 118140960795 + 3734293 * 2 ^ 59
def prefixEnd_3734293 : Nat := 4983230072969 + 3 ^ 40 * 3734293 * 2
def baseEnd_3734293 : Nat := 639162404573421098387935

theorem tailTrace_3734293 : CollatzResearch.WordTrace tailWord_3734293 prefixEnd_3734293 639162404573421098387935 := by
  unfold tailWord_3734293
  simp only [CollatzResearch.WordTrace]
  refine ⟨136200855060301702314327533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90800570040201134876218355 136200855060301702314327533)
  ·
    refine ⟨51075320647613138367872825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 136200855060301702314327533 51075320647613138367872825)
    ·
      refine ⟨38306490485709853775904619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51075320647613138367872825 38306490485709853775904619)
      ·
        refine ⟨57459735728564780663856929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38306490485709853775904619 57459735728564780663856929)
        ·
          refine ⟨43094801796423585497892697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57459735728564780663856929 43094801796423585497892697)
          ·
            refine ⟨32321101347317689123419523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43094801796423585497892697 32321101347317689123419523)
            ·
              refine ⟨48481652020976533685129285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32321101347317689123419523 48481652020976533685129285)
              ·
                refine ⟨9090309753933100065961741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48481652020976533685129285 9090309753933100065961741)
                ·
                  refine ⟨3408866157724912524735653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9090309753933100065961741 3408866157724912524735653)
                  ·
                    refine ⟨639162404573421098387935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3408866157724912524735653 639162404573421098387935)
                    ·
                      rfl

theorem cell23_3734293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 4, 3, 4].length) (baseStart_3734293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3734293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3734293 prefixEnd_3734293 := by exact prefixLift 3734293
  have htrace : WordTrace (prefixWord ++ tailWord_3734293) baseStart_3734293 baseEnd_3734293 := by
    simpa [prefixWord, tailWord_3734293, baseEnd_3734293] using wordTrace_append hprefix tailTrace_3734293
  have hstable : (prefixWord ++ tailWord_3734293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3734293).length < 2 ^ (prefixWord ++ tailWord_3734293).sum := by decide
  have hdescent : baseEnd_3734293 < baseStart_3734293 := by decide
  rcases family_descends (prefixWord ++ tailWord_3734293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3734296 : List Nat := [2, 1, 2, 3, 1, 1, 1, 1, 1, 6, 4]
def baseStart_3734296 : Nat := 118140960795 + 3734296 * 2 ^ 59
def prefixEnd_3734296 : Nat := 4983230072969 + 3 ^ 40 * 3734296 * 2
def baseEnd_3734296 : Nat := 1917488754162226783426291

theorem tailTrace_3734296 : CollatzResearch.WordTrace tailWord_3734296 prefixEnd_3734296 1917488754162226783426291 := by
  unfold tailWord_3734296
  simp only [CollatzResearch.WordTrace]
  refine ⟨68100482239645416913343371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90800642986193889217791161 68100482239645416913343371)
  ·
    refine ⟨102150723359468125370015057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68100482239645416913343371 102150723359468125370015057)
    ·
      refine ⟨76613042519601094027511293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102150723359468125370015057 76613042519601094027511293)
      ·
        refine ⟨28729890944850410260316735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76613042519601094027511293 28729890944850410260316735)
        ·
          refine ⟨43094836417275615390475103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28729890944850410260316735 43094836417275615390475103)
          ·
            refine ⟨64642254625913423085712655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43094836417275615390475103 64642254625913423085712655)
            ·
              refine ⟨96963381938870134628568983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64642254625913423085712655 96963381938870134628568983)
              ·
                refine ⟨145445072908305201942853475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 96963381938870134628568983 145445072908305201942853475)
                ·
                  refine ⟨218167609362457802914280213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 145445072908305201942853475 218167609362457802914280213)
                  ·
                    refine ⟨10226606688865209511606885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 218167609362457802914280213 10226606688865209511606885)
                    ·
                      refine ⟨1917488754162226783426291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10226606688865209511606885 1917488754162226783426291)
                      ·
                        rfl

theorem cell23_3734296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 1, 1, 6, 4].length) (baseStart_3734296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3734296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3734296 prefixEnd_3734296 := by exact prefixLift 3734296
  have htrace : WordTrace (prefixWord ++ tailWord_3734296) baseStart_3734296 baseEnd_3734296 := by
    simpa [prefixWord, tailWord_3734296, baseEnd_3734296] using wordTrace_append hprefix tailTrace_3734296
  have hstable : (prefixWord ++ tailWord_3734296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3734296).length < 2 ^ (prefixWord ++ tailWord_3734296).sum := by decide
  have hdescent : baseEnd_3734296 < baseStart_3734296 := by decide
  rcases family_descends (prefixWord ++ tailWord_3734296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3734303 : List Nat := [1, 1, 2, 4, 2, 2, 2, 1, 1, 4, 3]
def baseStart_3734303 : Nat := 118140960795 + 3734303 * 2 ^ 59
def prefixEnd_3734303 : Nat := 4983230072969 + 3 ^ 40 * 3734303 * 2
def baseEnd_3734303 : Nat := 1917492348526808256038759

theorem tailTrace_3734303 : CollatzResearch.WordTrace tailWord_3734303 prefixEnd_3734303 1917492348526808256038759 := by
  unfold tailWord_3734303
  simp only [CollatzResearch.WordTrace]
  refine ⟨136201219790265474022191563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90800813193510316014794375 136201219790265474022191563)
  ·
    refine ⟨204301829685398211033287345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136201219790265474022191563 204301829685398211033287345)
    ·
      refine ⟨153226372264048658274965509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 204301829685398211033287345 153226372264048658274965509)
      ·
        refine ⟨28729944799509123426556033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 153226372264048658274965509 28729944799509123426556033)
        ·
          refine ⟨21547458599631842569917025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28729944799509123426556033 21547458599631842569917025)
          ·
            refine ⟨16160593949723881927437769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21547458599631842569917025 16160593949723881927437769)
            ·
              refine ⟨12120445462292911445578327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16160593949723881927437769 12120445462292911445578327)
              ·
                refine ⟨18180668193439367168367491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12120445462292911445578327 18180668193439367168367491)
                ·
                  refine ⟨27271002290159050752551237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18180668193439367168367491 27271002290159050752551237)
                  ·
                    refine ⟨5113312929404822016103357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27271002290159050752551237 5113312929404822016103357)
                    ·
                      refine ⟨1917492348526808256038759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5113312929404822016103357 1917492348526808256038759)
                      ·
                        rfl

theorem cell23_3734303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 2, 1, 1, 4, 3].length) (baseStart_3734303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3734303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3734303 prefixEnd_3734303 := by exact prefixLift 3734303
  have htrace : WordTrace (prefixWord ++ tailWord_3734303) baseStart_3734303 baseEnd_3734303 := by
    simpa [prefixWord, tailWord_3734303, baseEnd_3734303] using wordTrace_append hprefix tailTrace_3734303
  have hstable : (prefixWord ++ tailWord_3734303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3734303).length < 2 ^ (prefixWord ++ tailWord_3734303).sum := by decide
  have hdescent : baseEnd_3734303 < baseStart_3734303 := by decide
  rcases family_descends (prefixWord ++ tailWord_3734303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3734327 : List Nat := [1, 1, 3, 1, 2, 1, 7, 2, 1, 4]
def baseStart_3734327 : Nat := 118140960795 + 3734327 * 2 ^ 59
def prefixEnd_3734327 : Nat := 4983230072969 + 3 ^ 40 * 3734327 * 2
def baseEnd_3734327 : Nat := 639168224020838720712883

theorem tailTrace_3734327 : CollatzResearch.WordTrace tailWord_3734327 prefixEnd_3734327 639168224020838720712883 := by
  unfold tailWord_3734327
  simp only [CollatzResearch.WordTrace]
  refine ⟨136202095142178526121065235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90801396761452350747376823 136202095142178526121065235)
  ·
    refine ⟨204303142713267789181597853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136202095142178526121065235 204303142713267789181597853)
    ·
      refine ⟨76613678517475420943099195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 204303142713267789181597853 76613678517475420943099195)
      ·
        refine ⟨114920517776213131414648793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76613678517475420943099195 114920517776213131414648793)
        ·
          refine ⟨86190388332159848560986595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114920517776213131414648793 86190388332159848560986595)
          ·
            refine ⟨129285582498239772841479893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86190388332159848560986595 129285582498239772841479893)
            ·
              refine ⟨3030130839802494675972185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 129285582498239772841479893 3030130839802494675972185)
              ·
                refine ⟨2272598129851871006979139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3030130839802494675972185 2272598129851871006979139)
                ·
                  refine ⟨3408897194777806510468709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2272598129851871006979139 3408897194777806510468709)
                  ·
                    refine ⟨639168224020838720712883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3408897194777806510468709 639168224020838720712883)
                    ·
                      rfl

theorem cell23_3734327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 7, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 7, 2, 1, 4].length) (baseStart_3734327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3734327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3734327 prefixEnd_3734327 := by exact prefixLift 3734327
  have htrace : WordTrace (prefixWord ++ tailWord_3734327) baseStart_3734327 baseEnd_3734327 := by
    simpa [prefixWord, tailWord_3734327, baseEnd_3734327] using wordTrace_append hprefix tailTrace_3734327
  have hstable : (prefixWord ++ tailWord_3734327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3734327).length < 2 ^ (prefixWord ++ tailWord_3734327).sum := by decide
  have hdescent : baseEnd_3734327 < baseStart_3734327 := by decide
  rcases family_descends (prefixWord ++ tailWord_3734327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3734346 : List Nat := [3, 1, 2, 1, 1, 1, 2, 1, 1, 3, 7]
def baseStart_3734346 : Nat := 118140960795 + 3734346 * 2 ^ 59
def prefixEnd_3734346 : Nat := 4983230072969 + 3 ^ 40 * 3734346 * 2
def baseEnd_3734346 : Nat := 1917514428194951587801061

theorem tailTrace_3734346 : CollatzResearch.WordTrace tailWord_3734346 prefixEnd_3734346 1917514428194951587801061 := by
  unfold tailWord_3734346
  simp only [CollatzResearch.WordTrace]
  refine ⟨34050697032277423091501723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90801858752739794910671261 34050697032277423091501723)
  ·
    refine ⟨51076045548416134637252585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34050697032277423091501723 51076045548416134637252585)
    ·
      refine ⟨38307034161312100977939439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51076045548416134637252585 38307034161312100977939439)
      ·
        refine ⟨57460551241968151466909159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38307034161312100977939439 57460551241968151466909159)
        ·
          refine ⟨86190826862952227200363739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57460551241968151466909159 86190826862952227200363739)
          ·
            refine ⟨129286240294428340800545609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86190826862952227200363739 129286240294428340800545609)
            ·
              refine ⟨96964680220821255600409207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 129286240294428340800545609 96964680220821255600409207)
              ·
                refine ⟨145447020331231883400613811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 96964680220821255600409207 145447020331231883400613811)
                ·
                  refine ⟨218170530496847825100920717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 145447020331231883400613811 218170530496847825100920717)
                  ·
                    refine ⟨81813948936317934412845269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 218170530496847825100920717 81813948936317934412845269)
                    ·
                      refine ⟨1917514428194951587801061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 81813948936317934412845269 1917514428194951587801061)
                      ·
                        rfl

theorem cell23_3734346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 1, 1, 3, 7].length) (baseStart_3734346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3734346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3734346 prefixEnd_3734346 := by exact prefixLift 3734346
  have htrace : WordTrace (prefixWord ++ tailWord_3734346) baseStart_3734346 baseEnd_3734346 := by
    simpa [prefixWord, tailWord_3734346, baseEnd_3734346] using wordTrace_append hprefix tailTrace_3734346
  have hstable : (prefixWord ++ tailWord_3734346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3734346).length < 2 ^ (prefixWord ++ tailWord_3734346).sum := by decide
  have hdescent : baseEnd_3734346 < baseStart_3734346 := by decide
  rcases family_descends (prefixWord ++ tailWord_3734346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3734350 : List Nat := [4, 1, 1, 1, 1, 1, 1, 6, 3, 1, 3]
def baseStart_3734350 : Nat := 118140960795 + 3734350 * 2 ^ 59
def prefixEnd_3734350 : Nat := 4983230072969 + 3 ^ 40 * 3734350 * 2
def baseEnd_3734350 : Nat := 1917516482117569572151043

theorem tailTrace_3734350 : CollatzResearch.WordTrace tailWord_3734350 prefixEnd_3734350 1917516482117569572151043 := by
  unfold tailWord_3734350
  simp only [CollatzResearch.WordTrace]
  refine ⟨17025366752636900131144063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 90801956014063467366101669 17025366752636900131144063)
  ·
    refine ⟨25538050128955350196716095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17025366752636900131144063 25538050128955350196716095)
    ·
      refine ⟨38307075193433025295074143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25538050128955350196716095 38307075193433025295074143)
      ·
        refine ⟨57460612790149537942611215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38307075193433025295074143 57460612790149537942611215)
        ·
          refine ⟨86190919185224306913916823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57460612790149537942611215 86190919185224306913916823)
          ·
            refine ⟨129286378777836460370875235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86190919185224306913916823 129286378777836460370875235)
            ·
              refine ⟨193929568166754690556312853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 129286378777836460370875235 193929568166754690556312853)
              ·
                refine ⟨9090448507816626119827165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 193929568166754690556312853 9090448507816626119827165)
                ·
                  refine ⟨3408918190431234794935187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9090448507816626119827165 3408918190431234794935187)
                  ·
                    refine ⟨5113377285646852192402781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3408918190431234794935187 5113377285646852192402781)
                    ·
                      refine ⟨1917516482117569572151043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5113377285646852192402781 1917516482117569572151043)
                      ·
                        rfl

theorem cell23_3734350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 6, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 6, 3, 1, 3].length) (baseStart_3734350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3734350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3734350 prefixEnd_3734350 := by exact prefixLift 3734350
  have htrace : WordTrace (prefixWord ++ tailWord_3734350) baseStart_3734350 baseEnd_3734350 := by
    simpa [prefixWord, tailWord_3734350, baseEnd_3734350] using wordTrace_append hprefix tailTrace_3734350
  have hstable : (prefixWord ++ tailWord_3734350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3734350).length < 2 ^ (prefixWord ++ tailWord_3734350).sum := by decide
  have hdescent : baseEnd_3734350 < baseStart_3734350 := by decide
  rcases family_descends (prefixWord ++ tailWord_3734350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3734367 : List Nat := [1, 1, 2, 3, 1, 3, 2, 5, 1, 1, 3]
def baseStart_3734367 : Nat := 118140960795 + 3734367 * 2 ^ 59
def prefixEnd_3734367 : Nat := 4983230072969 + 3 ^ 40 * 3734367 * 2
def baseEnd_3734367 : Nat := 1917525211288696005638465

theorem tailTrace_3734367 : CollatzResearch.WordTrace tailWord_3734367 prefixEnd_3734367 1917525211288696005638465 := by
  unfold tailWord_3734367
  simp only [CollatzResearch.WordTrace]
  refine ⟨136203554062033612952521355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90802369374689075301680903 136203554062033612952521355)
  ·
    refine ⟨204305331093050419428782033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136203554062033612952521355 204305331093050419428782033)
    ·
      refine ⟨153228998319787814571586525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 204305331093050419428782033 153228998319787814571586525)
      ·
        refine ⟨57460874369920430464344947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 153228998319787814571586525 57460874369920430464344947)
        ·
          refine ⟨86191311554880645696517421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57460874369920430464344947 86191311554880645696517421)
          ·
            refine ⟨32321741833080242136194033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 86191311554880645696517421 32321741833080242136194033)
            ·
              refine ⟨24241306374810181602145525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32321741833080242136194033 24241306374810181602145525)
              ·
                refine ⟨2272622472638454525201143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24241306374810181602145525 2272622472638454525201143)
                ·
                  refine ⟨3408933708957681787801715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2272622472638454525201143 3408933708957681787801715)
                  ·
                    refine ⟨5113400563436522681702573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3408933708957681787801715 5113400563436522681702573)
                    ·
                      refine ⟨1917525211288696005638465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5113400563436522681702573 1917525211288696005638465)
                      ·
                        rfl

theorem cell23_3734367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 2, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 2, 5, 1, 1, 3].length) (baseStart_3734367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3734367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3734367 prefixEnd_3734367 := by exact prefixLift 3734367
  have htrace : WordTrace (prefixWord ++ tailWord_3734367) baseStart_3734367 baseEnd_3734367 := by
    simpa [prefixWord, tailWord_3734367, baseEnd_3734367] using wordTrace_append hprefix tailTrace_3734367
  have hstable : (prefixWord ++ tailWord_3734367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3734367).length < 2 ^ (prefixWord ++ tailWord_3734367).sum := by decide
  have hdescent : baseEnd_3734367 < baseStart_3734367 := by decide
  rcases family_descends (prefixWord ++ tailWord_3734367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3734383 : List Nat := [1, 1, 2, 1, 3, 1, 1, 5, 4, 4]
def baseStart_3734383 : Nat := 118140960795 + 3734383 * 2 ^ 59
def prefixEnd_3734383 : Nat := 4983230072969 + 3 ^ 40 * 3734383 * 2
def baseEnd_3734383 : Nat := 639177808993055981012797

theorem tailTrace_3734383 : CollatzResearch.WordTrace tailWord_3734383 prefixEnd_3734383 639177808993055981012797 := by
  unfold tailWord_3734383
  simp only [CollatzResearch.WordTrace]
  refine ⟨136204137629975647685103803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90802758419983765123402535 136204137629975647685103803)
  ·
    refine ⟨204306206444963471527655705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136204137629975647685103803 204306206444963471527655705)
    ·
      refine ⟨153229654833722603645741779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 204306206444963471527655705 153229654833722603645741779)
      ·
        refine ⟨229844482250583905468612669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153229654833722603645741779 229844482250583905468612669)
        ·
          refine ⟨86191680843968964550729751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 229844482250583905468612669 86191680843968964550729751)
          ·
            refine ⟨129287521265953446826094627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86191680843968964550729751 129287521265953446826094627)
            ·
              refine ⟨193931281898930170239141941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 129287521265953446826094627 193931281898930170239141941)
              ·
                refine ⟨18181057678024703459919557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 193931281898930170239141941 18181057678024703459919557)
                ·
                  refine ⟨3408948314629631898734917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18181057678024703459919557 3408948314629631898734917)
                  ·
                    refine ⟨639177808993055981012797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3408948314629631898734917 639177808993055981012797)
                    ·
                      rfl

theorem cell23_3734383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 5, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 5, 4, 4].length) (baseStart_3734383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3734383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3734383 prefixEnd_3734383 := by exact prefixLift 3734383
  have htrace : WordTrace (prefixWord ++ tailWord_3734383) baseStart_3734383 baseEnd_3734383 := by
    simpa [prefixWord, tailWord_3734383, baseEnd_3734383] using wordTrace_append hprefix tailTrace_3734383
  have hstable : (prefixWord ++ tailWord_3734383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3734383).length < 2 ^ (prefixWord ++ tailWord_3734383).sum := by decide
  have hdescent : baseEnd_3734383 < baseStart_3734383 := by decide
  rcases family_descends (prefixWord ++ tailWord_3734383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3734384 : List Nat := [2, 1, 1, 1, 4, 1, 6, 2, 1, 1, 3]
def baseStart_3734384 : Nat := 118140960795 + 3734384 * 2 ^ 59
def prefixEnd_3734384 : Nat := 4983230072969 + 3 ^ 40 * 3734384 * 2
def baseEnd_3734384 : Nat := 1917533940459822439125887

theorem tailTrace_3734384 : CollatzResearch.WordTrace tailWord_3734384 prefixEnd_3734384 1917533940459822439125887 := by
  unfold tailWord_3734384
  simp only [CollatzResearch.WordTrace]
  refine ⟨68102087051486012427945103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90802782735314683237260137 68102087051486012427945103)
  ·
    refine ⟨102153130577229018641917655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68102087051486012427945103 102153130577229018641917655)
    ·
      refine ⟨153229695865843527962876483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102153130577229018641917655 153229695865843527962876483)
      ·
        refine ⟨229844543798765291944314725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153229695865843527962876483 229844543798765291944314725)
        ·
          refine ⟨43095851962268492239559011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 229844543798765291944314725 43095851962268492239559011)
          ·
            refine ⟨64643777943402738359338517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43095851962268492239559011 64643777943402738359338517)
            ·
              refine ⟨3030177091097003360593993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 64643777943402738359338517 3030177091097003360593993)
              ·
                refine ⟨2272632818322752520445495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3030177091097003360593993 2272632818322752520445495)
                ·
                  refine ⟨3408949227484128780668243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2272632818322752520445495 3408949227484128780668243)
                  ·
                    refine ⟨5113423841226193171002365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3408949227484128780668243 5113423841226193171002365)
                    ·
                      refine ⟨1917533940459822439125887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5113423841226193171002365 1917533940459822439125887)
                      ·
                        rfl

theorem cell23_3734384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 6, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 6, 2, 1, 1, 3].length) (baseStart_3734384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3734384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3734384 prefixEnd_3734384 := by exact prefixLift 3734384
  have htrace : WordTrace (prefixWord ++ tailWord_3734384) baseStart_3734384 baseEnd_3734384 := by
    simpa [prefixWord, tailWord_3734384, baseEnd_3734384] using wordTrace_append hprefix tailTrace_3734384
  have hstable : (prefixWord ++ tailWord_3734384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3734384).length < 2 ^ (prefixWord ++ tailWord_3734384).sum := by decide
  have hdescent : baseEnd_3734384 < baseStart_3734384 := by decide
  rcases family_descends (prefixWord ++ tailWord_3734384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3734407 : List Nat := [1, 1, 4, 2, 3, 1, 1, 1, 5, 2, 2]
def baseStart_3734407 : Nat := 118140960795 + 3734407 * 2 ^ 59
def prefixEnd_3734407 : Nat := 4983230072969 + 3 ^ 40 * 3734407 * 2
def baseEnd_3734407 : Nat := 1917545750514875849138281

theorem tailTrace_3734407 : CollatzResearch.WordTrace tailWord_3734407 prefixEnd_3734407 1917545750514875849138281 := by
  unfold tailWord_3734407
  simp only [CollatzResearch.WordTrace]
  refine ⟨136205012981888699783977475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90803341987925799855984983 136205012981888699783977475)
  ·
    refine ⟨204307519472833049675966213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136205012981888699783977475 204307519472833049675966213)
    ·
      refine ⟨38307659901156196814243665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 204307519472833049675966213 38307659901156196814243665)
      ·
        refine ⟨28730744925867147610682749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38307659901156196814243665 28730744925867147610682749)
        ·
          refine ⟨10774029347200180354006031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28730744925867147610682749 10774029347200180354006031)
          ·
            refine ⟨16161044020800270531009047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10774029347200180354006031 16161044020800270531009047)
            ·
              refine ⟨24241566031200405796513571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16161044020800270531009047 24241566031200405796513571)
              ·
                refine ⟨36362349046800608694770357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24241566031200405796513571 36362349046800608694770357)
                ·
                  refine ⟨3408970223137557065134721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 36362349046800608694770357 3408970223137557065134721)
                  ·
                    refine ⟨2556727667353167798851041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3408970223137557065134721 2556727667353167798851041)
                    ·
                      refine ⟨1917545750514875849138281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2556727667353167798851041 1917545750514875849138281)
                      ·
                        rfl

theorem cell23_3734407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 1, 1, 5, 2, 2].length) (baseStart_3734407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3734407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3734407 prefixEnd_3734407 := by exact prefixLift 3734407
  have htrace : WordTrace (prefixWord ++ tailWord_3734407) baseStart_3734407 baseEnd_3734407 := by
    simpa [prefixWord, tailWord_3734407, baseEnd_3734407] using wordTrace_append hprefix tailTrace_3734407
  have hstable : (prefixWord ++ tailWord_3734407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3734407).length < 2 ^ (prefixWord ++ tailWord_3734407).sum := by decide
  have hdescent : baseEnd_3734407 < baseStart_3734407 := by decide
  rcases family_descends (prefixWord ++ tailWord_3734407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3734420 : List Nat := [2, 4, 2, 1, 1, 1, 1, 4, 1, 2, 4]
def baseStart_3734420 : Nat := 118140960795 + 3734420 * 2 ^ 59
def prefixEnd_3734420 : Nat := 4983230072969 + 3 ^ 40 * 3734420 * 2
def baseEnd_3734420 : Nat := 1917552425763384298275721

theorem tailTrace_3734420 : CollatzResearch.WordTrace tailWord_3734420 prefixEnd_3734420 1917552425763384298275721 := by
  unfold tailWord_3734420
  simp only [CollatzResearch.WordTrace]
  refine ⟨68102743565420801502100357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90803658087227735336133809 68102743565420801502100357)
  ·
    refine ⟨12769264418516400281643817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 68102743565420801502100357 12769264418516400281643817)
    ·
      refine ⟨9576948313887300211232863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12769264418516400281643817 9576948313887300211232863)
      ·
        refine ⟨14365422470830950316849295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9576948313887300211232863 14365422470830950316849295)
        ·
          refine ⟨21548133706246425475273943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14365422470830950316849295 21548133706246425475273943)
          ·
            refine ⟨32322200559369638212910915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21548133706246425475273943 32322200559369638212910915)
            ·
              refine ⟨48483300839054457319366373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32322200559369638212910915 48483300839054457319366373)
              ·
                refine ⟨9090618907322710747381195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48483300839054457319366373 9090618907322710747381195)
                ·
                  refine ⟨13635928360984066121071793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9090618907322710747381195 13635928360984066121071793)
                  ·
                    refine ⟨10226946270738049590803845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13635928360984066121071793 10226946270738049590803845)
                    ·
                      refine ⟨1917552425763384298275721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10226946270738049590803845 1917552425763384298275721)
                      ·
                        rfl

theorem cell23_3734420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 4, 1, 2, 4].length) (baseStart_3734420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3734420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3734420 prefixEnd_3734420 := by exact prefixLift 3734420
  have htrace : WordTrace (prefixWord ++ tailWord_3734420) baseStart_3734420 baseEnd_3734420 := by
    simpa [prefixWord, tailWord_3734420, baseEnd_3734420] using wordTrace_append hprefix tailTrace_3734420
  have hstable : (prefixWord ++ tailWord_3734420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3734420).length < 2 ^ (prefixWord ++ tailWord_3734420).sum := by decide
  have hdescent : baseEnd_3734420 < baseStart_3734420 := by decide
  rcases family_descends (prefixWord ++ tailWord_3734420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3734434 : List Nat := [3, 3, 1, 2, 2, 3, 1, 2, 2, 4]
def baseStart_3734434 : Nat := 118140960795 + 3734434 * 2 ^ 59
def prefixEnd_3734434 : Nat := 4983230072969 + 3 ^ 40 * 3734434 * 2
def baseEnd_3734434 : Nat := 639186538164182414500219

theorem tailTrace_3734434 : CollatzResearch.WordTrace tailWord_3734434 prefixEnd_3734434 639186538164182414500219 := by
  unfold tailWord_3734434
  simp only [CollatzResearch.WordTrace]
  refine ⟨34051499438197720848802589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90803998501860588930140237 34051499438197720848802589)
  ·
    refine ⟨12769312289324145318300971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34051499438197720848802589 12769312289324145318300971)
    ·
      refine ⟨19153968433986217977451457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12769312289324145318300971 19153968433986217977451457)
      ·
        refine ⟨14365476325489663483088593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19153968433986217977451457 14365476325489663483088593)
        ·
          refine ⟨10774107244117247612316445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14365476325489663483088593 10774107244117247612316445)
          ·
            refine ⟨4040290216543967854618667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10774107244117247612316445 4040290216543967854618667)
            ·
              refine ⟨6060435324815951781928001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4040290216543967854618667 6060435324815951781928001)
              ·
                refine ⟨4545326493611963836446001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6060435324815951781928001 4545326493611963836446001)
                ·
                  refine ⟨3408994870208972877334501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4545326493611963836446001 3408994870208972877334501)
                  ·
                    refine ⟨639186538164182414500219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3408994870208972877334501 639186538164182414500219)
                    ·
                      rfl

theorem cell23_3734434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 3, 1, 2, 2, 4].length) (baseStart_3734434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3734434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3734434 prefixEnd_3734434 := by exact prefixLift 3734434
  have htrace : WordTrace (prefixWord ++ tailWord_3734434) baseStart_3734434 baseEnd_3734434 := by
    simpa [prefixWord, tailWord_3734434, baseEnd_3734434] using wordTrace_append hprefix tailTrace_3734434
  have hstable : (prefixWord ++ tailWord_3734434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3734434).length < 2 ^ (prefixWord ++ tailWord_3734434).sum := by decide
  have hdescent : baseEnd_3734434 < baseStart_3734434 := by decide
  rcases family_descends (prefixWord ++ tailWord_3734434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3734457 : List Nat := [1, 2, 1, 4, 2, 4, 1, 1, 1, 3, 3]
def baseStart_3734457 : Nat := 118140960795 + 3734457 * 2 ^ 59
def prefixEnd_3734457 : Nat := 4983230072969 + 3 ^ 40 * 3734457 * 2
def baseEnd_3734457 : Nat := 1917571424547600653513051

theorem tailTrace_3734457 : CollatzResearch.WordTrace tailWord_3734457 prefixEnd_3734457 1917571424547600653513051 := by
  unfold tailWord_3734457
  simp only [CollatzResearch.WordTrace]
  refine ⟨136206836631707558323297625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90804557754471705548865083 136206836631707558323297625)
  ·
    refine ⟨102155127473780668742473219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136206836631707558323297625 102155127473780668742473219)
    ·
      refine ⟨153232691210671003113709829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102155127473780668742473219 153232691210671003113709829)
      ·
        refine ⟨28731129602000813083820593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 153232691210671003113709829 28731129602000813083820593)
        ·
          refine ⟨21548347201500609812865445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28731129602000813083820593 21548347201500609812865445)
          ·
            refine ⟨4040315100281364339912271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21548347201500609812865445 4040315100281364339912271)
            ·
              refine ⟨6060472650422046509868407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4040315100281364339912271 6060472650422046509868407)
              ·
                refine ⟨9090708975633069764802611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6060472650422046509868407 9090708975633069764802611)
                ·
                  refine ⟨13636063463449604647203917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9090708975633069764802611 13636063463449604647203917)
                  ·
                    refine ⟨5113523798793601742701469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13636063463449604647203917 5113523798793601742701469)
                    ·
                      refine ⟨1917571424547600653513051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5113523798793601742701469 1917571424547600653513051)
                      ·
                        rfl

theorem cell23_3734457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 4, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 4, 1, 1, 1, 3, 3].length) (baseStart_3734457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3734457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3734457 prefixEnd_3734457 := by exact prefixLift 3734457
  have htrace : WordTrace (prefixWord ++ tailWord_3734457) baseStart_3734457 baseEnd_3734457 := by
    simpa [prefixWord, tailWord_3734457, baseEnd_3734457] using wordTrace_append hprefix tailTrace_3734457
  have hstable : (prefixWord ++ tailWord_3734457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3734457).length < 2 ^ (prefixWord ++ tailWord_3734457).sum := by decide
  have hdescent : baseEnd_3734457 < baseStart_3734457 := by decide
  rcases family_descends (prefixWord ++ tailWord_3734457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3734480 : List Nat := [2, 1, 1, 1, 1, 2, 3, 3, 3, 4, 2]
def baseStart_3734480 : Nat := 118140960795 + 3734480 * 2 ^ 59
def prefixEnd_3734480 : Nat := 4983230072969 + 3 ^ 40 * 3734480 * 2
def baseEnd_3734480 : Nat := 1917583234602654063525445

theorem tailTrace_3734480 : CollatzResearch.WordTrace tailWord_3734480 prefixEnd_3734480 1917583234602654063525445 := by
  unfold tailWord_3734480
  simp only [CollatzResearch.WordTrace]
  refine ⟨68103837755312116625692447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90805117007082822167589929 68103837755312116625692447)
  ·
    refine ⟨102155756632968174938538671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68103837755312116625692447 102155756632968174938538671)
    ·
      refine ⟨153233634949452262407808007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102155756632968174938538671 153233634949452262407808007)
      ·
        refine ⟨229850452424178393611712011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153233634949452262407808007 229850452424178393611712011)
        ·
          refine ⟨344775678636267590417568017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 229850452424178393611712011 344775678636267590417568017)
          ·
            refine ⟨258581758977200692813176013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 344775678636267590417568017 258581758977200692813176013)
            ·
              refine ⟨96968159616450259804941005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 258581758977200692813176013 96968159616450259804941005)
              ·
                refine ⟨36363059856168847426852877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 96968159616450259804941005 36363059856168847426852877)
                ·
                  refine ⟨13636147446063317785069829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36363059856168847426852877 13636147446063317785069829)
                  ·
                    refine ⟨2556777646136872084700593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13636147446063317785069829 2556777646136872084700593)
                    ·
                      refine ⟨1917583234602654063525445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2556777646136872084700593 1917583234602654063525445)
                      ·
                        rfl

theorem cell23_3734480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 3, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 3, 3, 4, 2].length) (baseStart_3734480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3734480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3734480 prefixEnd_3734480 := by exact prefixLift 3734480
  have htrace : WordTrace (prefixWord ++ tailWord_3734480) baseStart_3734480 baseEnd_3734480 := by
    simpa [prefixWord, tailWord_3734480, baseEnd_3734480] using wordTrace_append hprefix tailTrace_3734480
  have hstable : (prefixWord ++ tailWord_3734480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3734480).length < 2 ^ (prefixWord ++ tailWord_3734480).sum := by decide
  have hdescent : baseEnd_3734480 < baseStart_3734480 := by decide
  rcases family_descends (prefixWord ++ tailWord_3734480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3734484 : List Nat := [2, 4, 1, 2, 1, 2, 2, 3, 1, 3, 2]
def baseStart_3734484 : Nat := 118140960795 + 3734484 * 2 ^ 59
def prefixEnd_3734484 : Nat := 4983230072969 + 3 ^ 40 * 3734484 * 2
def baseEnd_3734484 : Nat := 1917585288525272047875427

theorem tailTrace_3734484 : CollatzResearch.WordTrace tailWord_3734484 prefixEnd_3734484 1917585288525272047875427 := by
  unfold tailWord_3734484
  simp only [CollatzResearch.WordTrace]
  refine ⟨68103910701304870967265253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90805214268406494623020337 68103910701304870967265253)
  ·
    refine ⟨12769483256494663306362235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 68103910701304870967265253 12769483256494663306362235)
    ·
      refine ⟨19154224884741994959543353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12769483256494663306362235 19154224884741994959543353)
      ·
        refine ⟨14365668663556496219657515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19154224884741994959543353 14365668663556496219657515)
        ·
          refine ⟨21548502995334744329486273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14365668663556496219657515 21548502995334744329486273)
          ·
            refine ⟨16161377246501058247114705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21548502995334744329486273 16161377246501058247114705)
            ·
              refine ⟨12121032934875793685336029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16161377246501058247114705 12121032934875793685336029)
              ·
                refine ⟨4545387350578422632001011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12121032934875793685336029 4545387350578422632001011)
                ·
                  refine ⟨6818081025867633948001517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4545387350578422632001011 6818081025867633948001517)
                  ·
                    refine ⟨2556780384700362730500569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6818081025867633948001517 2556780384700362730500569)
                    ·
                      refine ⟨1917585288525272047875427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2556780384700362730500569 1917585288525272047875427)
                      ·
                        rfl

theorem cell23_3734484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 2, 3, 1, 3, 2].length) (baseStart_3734484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3734484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3734484 prefixEnd_3734484 := by exact prefixLift 3734484
  have htrace : WordTrace (prefixWord ++ tailWord_3734484) baseStart_3734484 baseEnd_3734484 := by
    simpa [prefixWord, tailWord_3734484, baseEnd_3734484] using wordTrace_append hprefix tailTrace_3734484
  have hstable : (prefixWord ++ tailWord_3734484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3734484).length < 2 ^ (prefixWord ++ tailWord_3734484).sum := by decide
  have hdescent : baseEnd_3734484 < baseStart_3734484 := by decide
  rcases family_descends (prefixWord ++ tailWord_3734484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3734647 : List Nat := [1, 1, 3, 1, 1, 4, 1, 3, 1, 5, 2]
def baseStart_3734647 : Nat := 118140960795 + 3734647 * 2 ^ 59
def prefixEnd_3734647 : Nat := 4983230072969 + 3 ^ 40 * 3734647 * 2
def baseEnd_3734647 : Nat := 1917668985871954910137177

theorem tailTrace_3734647 : CollatzResearch.WordTrace tailWord_3734647 prefixEnd_3734647 1917668985871954910137177 := by
  unfold tailWord_3734647
  simp only [CollatzResearch.WordTrace]
  refine ⟨136213766501019220772714195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90809177667346147181809463 136213766501019220772714195)
  ·
    refine ⟨204320649751528831159071293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136213766501019220772714195 204320649751528831159071293)
    ·
      refine ⟨76620243656823311684651735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 204320649751528831159071293 76620243656823311684651735)
      ·
        refine ⟨114930365485234967526977603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76620243656823311684651735 114930365485234967526977603)
        ·
          refine ⟨172395548227852451290466405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114930365485234967526977603 172395548227852451290466405)
          ·
            refine ⟨32324165292722334616962451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 172395548227852451290466405 32324165292722334616962451)
            ·
              refine ⟨48486247939083501925443677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32324165292722334616962451 48486247939083501925443677)
              ·
                refine ⟨18182342977156313222041379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48486247939083501925443677 18182342977156313222041379)
                ·
                  refine ⟨27273514465734469833062069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18182342977156313222041379 27273514465734469833062069)
                  ·
                    refine ⟨2556891981162606546849569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 27273514465734469833062069 2556891981162606546849569)
                    ·
                      refine ⟨1917668985871954910137177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2556891981162606546849569 1917668985871954910137177)
                      ·
                        rfl

theorem cell23_3734647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 3, 1, 5, 2].length) (baseStart_3734647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3734647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3734647 prefixEnd_3734647 := by exact prefixLift 3734647
  have htrace : WordTrace (prefixWord ++ tailWord_3734647) baseStart_3734647 baseEnd_3734647 := by
    simpa [prefixWord, tailWord_3734647, baseEnd_3734647] using wordTrace_append hprefix tailTrace_3734647
  have hstable : (prefixWord ++ tailWord_3734647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3734647).length < 2 ^ (prefixWord ++ tailWord_3734647).sum := by decide
  have hdescent : baseEnd_3734647 < baseStart_3734647 := by decide
  rcases family_descends (prefixWord ++ tailWord_3734647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3734677 : List Nat := [1, 3, 2, 1, 1, 1, 2, 2, 2, 6, 2]
def baseStart_3734677 : Nat := 118140960795 + 3734677 * 2 ^ 59
def prefixEnd_3734677 : Nat := 4983230072969 + 3 ^ 40 * 3734677 * 2
def baseEnd_3734677 : Nat := 1917684390291589792762039

theorem tailTrace_3734677 : CollatzResearch.WordTrace tailWord_3734677 prefixEnd_3734677 1917684390291589792762039 := by
  unfold tailWord_3734677
  simp only [CollatzResearch.WordTrace]
  refine ⟨136214860690910535896306285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90809907127273690597537523 136214860690910535896306285)
  ·
    refine ⟨51080572759091450961114857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 136214860690910535896306285 51080572759091450961114857)
    ·
      refine ⟨38310429569318588220836143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51080572759091450961114857 38310429569318588220836143)
      ·
        refine ⟨57465644353977882331254215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38310429569318588220836143 57465644353977882331254215)
        ·
          refine ⟨86198466530966823496881323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57465644353977882331254215 86198466530966823496881323)
          ·
            refine ⟨129297699796450235245321985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86198466530966823496881323 129297699796450235245321985)
            ·
              refine ⟨96973274847337676433991489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 129297699796450235245321985 96973274847337676433991489)
              ·
                refine ⟨72729956135503257325493617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 96973274847337676433991489 72729956135503257325493617)
                ·
                  refine ⟨54547467101627442994120213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 72729956135503257325493617 54547467101627442994120213)
                  ·
                    refine ⟨2556912520388786390349385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 54547467101627442994120213 2556912520388786390349385)
                    ·
                      refine ⟨1917684390291589792762039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2556912520388786390349385 1917684390291589792762039)
                      ·
                        rfl

theorem cell23_3734677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 2, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 2, 2, 6, 2].length) (baseStart_3734677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3734677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3734677 prefixEnd_3734677 := by exact prefixLift 3734677
  have htrace : WordTrace (prefixWord ++ tailWord_3734677) baseStart_3734677 baseEnd_3734677 := by
    simpa [prefixWord, tailWord_3734677, baseEnd_3734677] using wordTrace_append hprefix tailTrace_3734677
  have hstable : (prefixWord ++ tailWord_3734677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3734677).length < 2 ^ (prefixWord ++ tailWord_3734677).sum := by decide
  have hdescent : baseEnd_3734677 < baseStart_3734677 := by decide
  rcases family_descends (prefixWord ++ tailWord_3734677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3734698 : List Nat := [3, 1, 5, 1, 1, 2, 2, 1, 2, 3, 2]
def baseStart_3734698 : Nat := 118140960795 + 3734698 * 2 ^ 59
def prefixEnd_3734698 : Nat := 4983230072969 + 3 ^ 40 * 3734698 * 2
def baseEnd_3734698 : Nat := 1917695173385334210599443

theorem tailTrace_3734698 : CollatzResearch.WordTrace tailWord_3734698 prefixEnd_3734698 1917695173385334210599443 := by
  unfold tailWord_3734698
  simp only [CollatzResearch.WordTrace]
  refine ⟨34053906655958614120705187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90810417749222970988547165 34053906655958614120705187)
  ·
    refine ⟨51080859983937921181057781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34053906655958614120705187 51080859983937921181057781)
    ·
      refine ⟨4788830623494180110724167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 51080859983937921181057781 4788830623494180110724167)
      ·
        refine ⟨7183245935241270166086251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4788830623494180110724167 7183245935241270166086251)
        ·
          refine ⟨10774868902861905249129377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7183245935241270166086251 10774868902861905249129377)
          ·
            refine ⟨8081151677146428936847033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10774868902861905249129377 8081151677146428936847033)
            ·
              refine ⟨6060863757859821702635275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8081151677146428936847033 6060863757859821702635275)
              ·
                refine ⟨9091295636789732553952913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6060863757859821702635275 9091295636789732553952913)
                ·
                  refine ⟨6818471727592299415464685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9091295636789732553952913 6818471727592299415464685)
                  ·
                    refine ⟨2556926897847112280799257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6818471727592299415464685 2556926897847112280799257)
                    ·
                      refine ⟨1917695173385334210599443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2556926897847112280799257 1917695173385334210599443)
                      ·
                        rfl

theorem cell23_3734698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 2, 1, 2, 3, 2].length) (baseStart_3734698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3734698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3734698 prefixEnd_3734698 := by exact prefixLift 3734698
  have htrace : WordTrace (prefixWord ++ tailWord_3734698) baseStart_3734698 baseEnd_3734698 := by
    simpa [prefixWord, tailWord_3734698, baseEnd_3734698] using wordTrace_append hprefix tailTrace_3734698
  have hstable : (prefixWord ++ tailWord_3734698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3734698).length < 2 ^ (prefixWord ++ tailWord_3734698).sum := by decide
  have hdescent : baseEnd_3734698 < baseStart_3734698 := by decide
  rcases family_descends (prefixWord ++ tailWord_3734698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3734721 : List Nat := [1, 2, 6, 1, 1, 1, 1, 4, 2, 4]
def baseStart_3734721 : Nat := 118140960795 + 3734721 * 2 ^ 59
def prefixEnd_3734721 : Nat := 4983230072969 + 3 ^ 40 * 3734721 * 2
def baseEnd_3734721 : Nat := 639235661146795873537279

theorem tailTrace_3734721 : CollatzResearch.WordTrace tailWord_3734721 prefixEnd_3734721 639235661146795873537279 := by
  unfold tailWord_3734721
  simp only [CollatzResearch.WordTrace]
  refine ⟨136216465502751131410908017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90810977001834087607272011 136216465502751131410908017)
  ·
    refine ⟨102162349127063348558181013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136216465502751131410908017 102162349127063348558181013)
    ·
      refine ⟨4788860115331094463664735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 102162349127063348558181013 4788860115331094463664735)
      ·
        refine ⟨7183290172996641695497103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4788860115331094463664735 7183290172996641695497103)
        ·
          refine ⟨10774935259494962543245655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7183290172996641695497103 10774935259494962543245655)
          ·
            refine ⟨16162402889242443814868483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10774935259494962543245655 16162402889242443814868483)
            ·
              refine ⟨24243604333863665722302725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16162402889242443814868483 24243604333863665722302725)
              ·
                refine ⟨4545675812599437322931761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24243604333863665722302725 4545675812599437322931761)
                ·
                  refine ⟨3409256859449577992198821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4545675812599437322931761 3409256859449577992198821)
                  ·
                    refine ⟨639235661146795873537279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3409256859449577992198821 639235661146795873537279)
                    ·
                      rfl

theorem cell23_3734721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 1, 4, 2, 4].length) (baseStart_3734721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3734721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3734721 prefixEnd_3734721 := by exact prefixLift 3734721
  have htrace : WordTrace (prefixWord ++ tailWord_3734721) baseStart_3734721 baseEnd_3734721 := by
    simpa [prefixWord, tailWord_3734721, baseEnd_3734721] using wordTrace_append hprefix tailTrace_3734721
  have hstable : (prefixWord ++ tailWord_3734721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3734721).length < 2 ^ (prefixWord ++ tailWord_3734721).sum := by decide
  have hdescent : baseEnd_3734721 < baseStart_3734721 := by decide
  rcases family_descends (prefixWord ++ tailWord_3734721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3734722 : List Nat := [3, 5, 1, 1, 2, 1, 1, 4, 1, 1, 3]
def baseStart_3734722 : Nat := 118140960795 + 3734722 * 2 ^ 59
def prefixEnd_3734722 : Nat := 4983230072969 + 3 ^ 40 * 3734722 * 2
def baseEnd_3734722 : Nat := 1917707496921042116699333

theorem tailTrace_3734722 : CollatzResearch.WordTrace tailWord_3734722 prefixEnd_3734722 1917707496921042116699333 := by
  unfold tailWord_3734722
  simp only [CollatzResearch.WordTrace]
  refine ⟨34054125493936877145423605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90811001317165005721129613 34054125493936877145423605)
  ·
    refine ⟨3192574265056582232383463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 34054125493936877145423605 3192574265056582232383463)
    ·
      refine ⟨4788861397584873348575195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3192574265056582232383463 4788861397584873348575195)
      ·
        refine ⟨7183292096377310022862793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4788861397584873348575195 7183292096377310022862793)
        ·
          refine ⟨5387469072282982517147095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7183292096377310022862793 5387469072282982517147095)
          ·
            refine ⟨8081203608424473775720643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5387469072282982517147095 8081203608424473775720643)
            ·
              refine ⟨12121805412636710663580965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8081203608424473775720643 12121805412636710663580965)
              ·
                refine ⟨2272838514869383249421431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12121805412636710663580965 2272838514869383249421431)
                ·
                  refine ⟨3409257772304074874132147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2272838514869383249421431 3409257772304074874132147)
                  ·
                    refine ⟨5113886658456112311198221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3409257772304074874132147 5113886658456112311198221)
                    ·
                      refine ⟨1917707496921042116699333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5113886658456112311198221 1917707496921042116699333)
                      ·
                        rfl

theorem cell23_3734722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 1, 4, 1, 1, 3].length) (baseStart_3734722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3734722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3734722 prefixEnd_3734722 := by exact prefixLift 3734722
  have htrace : WordTrace (prefixWord ++ tailWord_3734722) baseStart_3734722 baseEnd_3734722 := by
    simpa [prefixWord, tailWord_3734722, baseEnd_3734722] using wordTrace_append hprefix tailTrace_3734722
  have hstable : (prefixWord ++ tailWord_3734722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3734722).length < 2 ^ (prefixWord ++ tailWord_3734722).sum := by decide
  have hdescent : baseEnd_3734722 < baseStart_3734722 := by decide
  rcases family_descends (prefixWord ++ tailWord_3734722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3734734 : List Nat := [4, 1, 1, 1, 5, 2, 1, 8]
def baseStart_3734734 : Nat := 118140960795 + 3734734 * 2 ^ 59
def prefixEnd_3734734 : Nat := 4983230072969 + 3 ^ 40 * 3734734 * 2
def baseEnd_3734734 : Nat := 71026431803292447027751

theorem tailTrace_3734734 : CollatzResearch.WordTrace tailWord_3734734 prefixEnd_3734734 71026431803292447027751 := by
  unfold tailWord_3734734
  simp only [CollatzResearch.WordTrace]
  refine ⟨17027117456463004328891407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 90811293101136023087420837 17027117456463004328891407)
  ·
    refine ⟨25540676184694506493337111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17027117456463004328891407 25540676184694506493337111)
    ·
      refine ⟨38311014277041759740005667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25540676184694506493337111 38311014277041759740005667)
      ·
        refine ⟨57466521415562639610008501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38311014277041759740005667 57466521415562639610008501)
        ·
          refine ⟨5387486382708997463438297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 57466521415562639610008501 5387486382708997463438297)
          ·
            refine ⟨4040614787031748097578723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5387486382708997463438297 4040614787031748097578723)
            ·
              refine ⟨6060922180547622146368085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4040614787031748097578723 6060922180547622146368085)
              ·
                refine ⟨71026431803292447027751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6060922180547622146368085 71026431803292447027751)
                ·
                  rfl

theorem cell23_3734734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 2, 1, 8].length) (baseStart_3734734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3734734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3734734 prefixEnd_3734734 := by exact prefixLift 3734734
  have htrace : WordTrace (prefixWord ++ tailWord_3734734) baseStart_3734734 baseEnd_3734734 := by
    simpa [prefixWord, tailWord_3734734, baseEnd_3734734] using wordTrace_append hprefix tailTrace_3734734
  have hstable : (prefixWord ++ tailWord_3734734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3734734).length < 2 ^ (prefixWord ++ tailWord_3734734).sum := by decide
  have hdescent : baseEnd_3734734 < baseStart_3734734 := by decide
  rcases family_descends (prefixWord ++ tailWord_3734734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3734771 : List Nat := [1, 1, 1, 2, 2, 6, 1, 3, 1, 3, 2]
def baseStart_3734771 : Nat := 118140960795 + 3734771 * 2 ^ 59
def prefixEnd_3734771 : Nat := 4983230072969 + 3 ^ 40 * 3734771 * 2
def baseEnd_3734771 : Nat := 1917732657473112424986607

theorem tailTrace_3734771 : CollatzResearch.WordTrace tailWord_3734771 prefixEnd_3734771 1917732657473112424986607 := by
  unfold tailWord_3734771
  simp only [CollatzResearch.WordTrace]
  refine ⟨136218289152569989950228167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90812192768379993300152111 136218289152569989950228167)
  ·
    refine ⟨204327433728854984925342251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136218289152569989950228167 204327433728854984925342251)
    ·
      refine ⟨306491150593282477388013377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204327433728854984925342251 306491150593282477388013377)
      ·
        refine ⟨229868362944961858041010033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 306491150593282477388013377 229868362944961858041010033)
        ·
          refine ⟨172401272208721393530757525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 229868362944961858041010033 172401272208721393530757525)
          ·
            refine ⟨8081309634783815321754259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 172401272208721393530757525 8081309634783815321754259)
            ·
              refine ⟨12121964452175722982631389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8081309634783815321754259 12121964452175722982631389)
              ·
                refine ⟨4545736669565896118486771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12121964452175722982631389 4545736669565896118486771)
                ·
                  refine ⟨6818605004348844177730157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4545736669565896118486771 6818605004348844177730157)
                  ·
                    refine ⟨2556976876630816566648809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6818605004348844177730157 2556976876630816566648809)
                    ·
                      refine ⟨1917732657473112424986607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2556976876630816566648809 1917732657473112424986607)
                      ·
                        rfl

theorem cell23_3734771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 1, 3, 1, 3, 2].length) (baseStart_3734771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3734771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3734771 prefixEnd_3734771 := by exact prefixLift 3734771
  have htrace : WordTrace (prefixWord ++ tailWord_3734771) baseStart_3734771 baseEnd_3734771 := by
    simpa [prefixWord, tailWord_3734771, baseEnd_3734771] using wordTrace_append hprefix tailTrace_3734771
  have hstable : (prefixWord ++ tailWord_3734771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3734771).length < 2 ^ (prefixWord ++ tailWord_3734771).sum := by decide
  have hdescent : baseEnd_3734771 < baseStart_3734771 := by decide
  rcases family_descends (prefixWord ++ tailWord_3734771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3734772 : List Nat := [2, 6, 1, 2, 1, 2, 1, 2, 2, 4]
def baseStart_3734772 : Nat := 118140960795 + 3734772 * 2 ^ 59
def prefixEnd_3734772 : Nat := 4983230072969 + 3 ^ 40 * 3734772 * 2
def baseEnd_3734772 : Nat := 639244390317922307024701

theorem tailTrace_3734772 : CollatzResearch.WordTrace tailWord_3734772 prefixEnd_3734772 639244390317922307024701 := by
  unfold tailWord_3734772
  simp only [CollatzResearch.WordTrace]
  refine ⟨68109162812783183560507285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90812217083710911414009713 68109162812783183560507285)
  ·
    refine ⟨3192617006849211729398779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 68109162812783183560507285 3192617006849211729398779)
    ·
      refine ⟨4788925510273817594098169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3192617006849211729398779 4788925510273817594098169)
      ·
        refine ⟨3591694132705363195573627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4788925510273817594098169 3591694132705363195573627)
        ·
          refine ⟨5387541199058044793360441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3591694132705363195573627 5387541199058044793360441)
          ·
            refine ⟨4040655899293533595020331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5387541199058044793360441 4040655899293533595020331)
            ·
              refine ⟨6060983848940300392530497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4040655899293533595020331 6060983848940300392530497)
              ·
                refine ⟨4545737886705225294397873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6060983848940300392530497 4545737886705225294397873)
                ·
                  refine ⟨3409303415028918970798405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4545737886705225294397873 3409303415028918970798405)
                  ·
                    refine ⟨639244390317922307024701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3409303415028918970798405 639244390317922307024701)
                    ·
                      rfl

theorem cell23_3734772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 2, 1, 2, 2, 4].length) (baseStart_3734772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3734772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3734772 prefixEnd_3734772 := by exact prefixLift 3734772
  have htrace : WordTrace (prefixWord ++ tailWord_3734772) baseStart_3734772 baseEnd_3734772 := by
    simpa [prefixWord, tailWord_3734772, baseEnd_3734772] using wordTrace_append hprefix tailTrace_3734772
  have hstable : (prefixWord ++ tailWord_3734772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3734772).length < 2 ^ (prefixWord ++ tailWord_3734772).sum := by decide
  have hdescent : baseEnd_3734772 < baseStart_3734772 := by decide
  rcases family_descends (prefixWord ++ tailWord_3734772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3734807 : List Nat := [1, 1, 3, 4, 1, 1, 1, 4, 7]
def baseStart_3734807 : Nat := 118140960795 + 3734807 * 2 ^ 59
def prefixEnd_3734807 : Nat := 4983230072969 + 3 ^ 40 * 3734807 * 2
def baseEnd_3734807 : Nat := 213083460308519364904049

theorem tailTrace_3734807 : CollatzResearch.WordTrace tailWord_3734807 prefixEnd_3734807 213083460308519364904049 := by
  unfold tailWord_3734807
  simp only [CollatzResearch.WordTrace]
  refine ⟨136219602180439568098538675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90813068120293045399025783 136219602180439568098538675)
  ·
    refine ⟨204329403270659352147808013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136219602180439568098538675 204329403270659352147808013)
    ·
      refine ⟨76623526226497257055428005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 204329403270659352147808013 76623526226497257055428005)
      ·
        refine ⟨14366911167468235697892751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 76623526226497257055428005 14366911167468235697892751)
        ·
          refine ⟨21550366751202353546839127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14366911167468235697892751 21550366751202353546839127)
          ·
            refine ⟨32325550126803530320258691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21550366751202353546839127 32325550126803530320258691)
            ·
              refine ⟨48488325190205295480388037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32325550126803530320258691 48488325190205295480388037)
              ·
                refine ⟨9091560973163492902572757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48488325190205295480388037 9091560973163492902572757)
                ·
                  refine ⟨213083460308519364904049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9091560973163492902572757 213083460308519364904049)
                  ·
                    rfl

theorem cell23_3734807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 4, 7].length) (baseStart_3734807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3734807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3734807 prefixEnd_3734807 := by exact prefixLift 3734807
  have htrace : WordTrace (prefixWord ++ tailWord_3734807) baseStart_3734807 baseEnd_3734807 := by
    simpa [prefixWord, tailWord_3734807, baseEnd_3734807] using wordTrace_append hprefix tailTrace_3734807
  have hstable : (prefixWord ++ tailWord_3734807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3734807).length < 2 ^ (prefixWord ++ tailWord_3734807).sum := by decide
  have hdescent : baseEnd_3734807 < baseStart_3734807 := by decide
  rcases family_descends (prefixWord ++ tailWord_3734807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3734841 : List Nat := [1, 2, 1, 6, 2, 2, 1, 1, 7]
def baseStart_3734841 : Nat := 118140960795 + 3734841 * 2 ^ 59
def prefixEnd_3734841 : Nat := 4983230072969 + 3 ^ 40 * 3734841 * 2
def baseEnd_3734841 : Nat := 213085400124325239012365

theorem tailTrace_3734841 : CollatzResearch.WordTrace tailWord_3734841 prefixEnd_3734841 213085400124325239012365 := by
  unfold tailWord_3734841
  simp only [CollatzResearch.WordTrace]
  refine ⟨136220842262316391905276377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90813894841544261270184251 136220842262316391905276377)
  ·
    refine ⟨102165631696737293928957283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136220842262316391905276377 102165631696737293928957283)
    ·
      refine ⟨153248447545105940893435925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102165631696737293928957283 153248447545105940893435925)
      ·
        refine ⟨7183520978676840979379809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 153248447545105940893435925 7183520978676840979379809)
        ·
          refine ⟨5387640734007630734534857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7183520978676840979379809 5387640734007630734534857)
          ·
            refine ⟨4040730550505723050901143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5387640734007630734534857 4040730550505723050901143)
            ·
              refine ⟨6061095825758584576351715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4040730550505723050901143 6061095825758584576351715)
              ·
                refine ⟨9091643738637876864527573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6061095825758584576351715 9091643738637876864527573)
                ·
                  refine ⟨213085400124325239012365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9091643738637876864527573 213085400124325239012365)
                  ·
                    rfl

theorem cell23_3734841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 2, 1, 1, 7].length) (baseStart_3734841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3734841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3734841 prefixEnd_3734841 := by exact prefixLift 3734841
  have htrace : WordTrace (prefixWord ++ tailWord_3734841) baseStart_3734841 baseEnd_3734841 := by
    simpa [prefixWord, tailWord_3734841, baseEnd_3734841] using wordTrace_append hprefix tailTrace_3734841
  have hstable : (prefixWord ++ tailWord_3734841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3734841).length < 2 ^ (prefixWord ++ tailWord_3734841).sum := by decide
  have hdescent : baseEnd_3734841 < baseStart_3734841 := by decide
  rcases family_descends (prefixWord ++ tailWord_3734841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3734847 : List Nat := [1, 1, 2, 2, 4, 2, 1, 1, 1, 1, 7]
def baseStart_3734847 : Nat := 118140960795 + 3734847 * 2 ^ 59
def prefixEnd_3734847 : Nat := 4983230072969 + 3 ^ 40 * 3734847 * 2
def baseEnd_3734847 : Nat := 1917771682002854127636257

theorem tailTrace_3734847 : CollatzResearch.WordTrace tailWord_3734847 prefixEnd_3734847 1917771682002854127636257 := by
  unfold tailWord_3734847
  simp only [CollatzResearch.WordTrace]
  refine ⟨136221061100294654929994795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90814040733529769953329863 136221061100294654929994795)
  ·
    refine ⟨204331591650441982394992193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136221061100294654929994795 204331591650441982394992193)
    ·
      refine ⟨153248693737831486796244145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 204331591650441982394992193 153248693737831486796244145)
      ·
        refine ⟨114936520303373615097183109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 153248693737831486796244145 114936520303373615097183109)
        ·
          refine ⟨21550597556882552830721833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 114936520303373615097183109 21550597556882552830721833)
          ·
            refine ⟨16162948167661914623041375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21550597556882552830721833 16162948167661914623041375)
            ·
              refine ⟨24244422251492871934562063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16162948167661914623041375 24244422251492871934562063)
              ·
                refine ⟨36366633377239307901843095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24244422251492871934562063 36366633377239307901843095)
                ·
                  refine ⟨54549950065858961852764643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36366633377239307901843095 54549950065858961852764643)
                  ·
                    refine ⟨81824925098788442779146965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 54549950065858961852764643 81824925098788442779146965)
                    ·
                      refine ⟨1917771682002854127636257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 81824925098788442779146965 1917771682002854127636257)
                      ·
                        rfl

theorem cell23_3734847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 1, 1, 1, 1, 7].length) (baseStart_3734847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3734847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3734847 prefixEnd_3734847 := by exact prefixLift 3734847
  have htrace : WordTrace (prefixWord ++ tailWord_3734847) baseStart_3734847 baseEnd_3734847 := by
    simpa [prefixWord, tailWord_3734847, baseEnd_3734847] using wordTrace_append hprefix tailTrace_3734847
  have hstable : (prefixWord ++ tailWord_3734847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3734847).length < 2 ^ (prefixWord ++ tailWord_3734847).sum := by decide
  have hdescent : baseEnd_3734847 < baseStart_3734847 := by decide
  rcases family_descends (prefixWord ++ tailWord_3734847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3734852 : List Nat := [2, 3, 4, 1, 1, 1, 4, 1, 2, 2, 2]
def baseStart_3734852 : Nat := 118140960795 + 3734852 * 2 ^ 59
def prefixEnd_3734852 : Nat := 4983230072969 + 3 ^ 40 * 3734852 * 2
def baseEnd_3734852 : Nat := 1917774249406126608073735

theorem tailTrace_3734852 : CollatzResearch.WordTrace tailWord_3734852 prefixEnd_3734852 1917774249406126608073735 := by
  unfold tailWord_3734852
  simp only [CollatzResearch.WordTrace]
  refine ⟨68110621732638270391963405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90814162310184360522617873 68110621732638270391963405)
  ·
    refine ⟨25541483149739351396986277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68110621732638270391963405 25541483149739351396986277)
    ·
      refine ⟨4789028090576128386934927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25541483149739351396986277 4789028090576128386934927)
      ·
        refine ⟨7183542135864192580402391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4789028090576128386934927 7183542135864192580402391)
        ·
          refine ⟨10775313203796288870603587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7183542135864192580402391 10775313203796288870603587)
          ·
            refine ⟨16162969805694433305905381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10775313203796288870603587 16162969805694433305905381)
            ·
              refine ⟨3030556838567706244857259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16162969805694433305905381 3030556838567706244857259)
              ·
                refine ⟨4545835257851559367285889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3030556838567706244857259 4545835257851559367285889)
                ·
                  refine ⟨3409376443388669525464417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4545835257851559367285889 3409376443388669525464417)
                  ·
                    refine ⟨2557032332541502144098313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3409376443388669525464417 2557032332541502144098313)
                    ·
                      refine ⟨1917774249406126608073735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2557032332541502144098313 1917774249406126608073735)
                      ·
                        rfl

theorem cell23_3734852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 4, 1, 2, 2, 2].length) (baseStart_3734852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3734852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3734852 prefixEnd_3734852 := by exact prefixLift 3734852
  have htrace : WordTrace (prefixWord ++ tailWord_3734852) baseStart_3734852 baseEnd_3734852 := by
    simpa [prefixWord, tailWord_3734852, baseEnd_3734852] using wordTrace_append hprefix tailTrace_3734852
  have hstable : (prefixWord ++ tailWord_3734852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3734852).length < 2 ^ (prefixWord ++ tailWord_3734852).sum := by decide
  have hdescent : baseEnd_3734852 < baseStart_3734852 := by decide
  rcases family_descends (prefixWord ++ tailWord_3734852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3734857 : List Nat := [1, 2, 1, 1, 2, 3, 2, 1, 3, 3, 4]
def baseStart_3734857 : Nat := 118140960795 + 3734857 * 2 ^ 59
def prefixEnd_3734857 : Nat := 4983230072969 + 3 ^ 40 * 3734857 * 2
def baseEnd_3734857 : Nat := 1917776816809399088511211

theorem tailTrace_3734857 : CollatzResearch.WordTrace tailWord_3734857 prefixEnd_3734857 1917776816809399088511211 := by
  unfold tailWord_3734857
  simp only [CollatzResearch.WordTrace]
  refine ⟨136221425830258426637858825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90814283886838951091905883 136221425830258426637858825)
  ·
    refine ⟨102166069372693819978394119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136221425830258426637858825 102166069372693819978394119)
    ·
      refine ⟨153249104059040729967591179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102166069372693819978394119 153249104059040729967591179)
      ·
        refine ⟨229873656088561094951386769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153249104059040729967591179 229873656088561094951386769)
        ·
          refine ⟨172405242066420821213540077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 229873656088561094951386769 172405242066420821213540077)
          ·
            refine ⟨64651965774907807955077529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 172405242066420821213540077 64651965774907807955077529)
            ·
              refine ⟨48488974331180855966308147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64651965774907807955077529 48488974331180855966308147)
              ·
                refine ⟨72733461496771283949462221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48488974331180855966308147 72733461496771283949462221)
                ·
                  refine ⟨27275048061289231481048333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 72733461496771283949462221 27275048061289231481048333)
                  ·
                    refine ⟨10228143022983461805393125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27275048061289231481048333 10228143022983461805393125)
                    ·
                      refine ⟨1917776816809399088511211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10228143022983461805393125 1917776816809399088511211)
                      ·
                        rfl

theorem cell23_3734857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 1, 3, 3, 4].length) (baseStart_3734857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3734857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3734857 prefixEnd_3734857 := by exact prefixLift 3734857
  have htrace : WordTrace (prefixWord ++ tailWord_3734857) baseStart_3734857 baseEnd_3734857 := by
    simpa [prefixWord, tailWord_3734857, baseEnd_3734857] using wordTrace_append hprefix tailTrace_3734857
  have hstable : (prefixWord ++ tailWord_3734857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3734857).length < 2 ^ (prefixWord ++ tailWord_3734857).sum := by decide
  have hdescent : baseEnd_3734857 < baseStart_3734857 := by decide
  rcases family_descends (prefixWord ++ tailWord_3734857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3734874 : List Nat := [3, 1, 1, 2, 1, 2, 3, 3, 2, 1, 4]
def baseStart_3734874 : Nat := 118140960795 + 3734874 * 2 ^ 59
def prefixEnd_3734874 : Nat := 4983230072969 + 3 ^ 40 * 3734874 * 2
def baseEnd_3734874 : Nat := 1917785545980525521998633

theorem tailTrace_3734874 : CollatzResearch.WordTrace tailWord_3734874 prefixEnd_3734874 1917785545980525521998633 := by
  unfold tailWord_3734874
  simp only [CollatzResearch.WordTrace]
  refine ⟨34055511467799209635306919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90814697247464559027485117 34055511467799209635306919)
  ·
    refine ⟨51083267201698814452960379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34055511467799209635306919 51083267201698814452960379)
    ·
      refine ⟨76624900802548221679440569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51083267201698814452960379 76624900802548221679440569)
      ·
        refine ⟨57468675601911166259580427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76624900802548221679440569 57468675601911166259580427)
        ·
          refine ⟨86203013402866749389370641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57468675601911166259580427 86203013402866749389370641)
          ·
            refine ⟨64652260052150062042027981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86203013402866749389370641 64652260052150062042027981)
            ·
              refine ⟨24244597519556273265760493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64652260052150062042027981 24244597519556273265760493)
              ·
                refine ⟨9091724069833602474660185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24244597519556273265760493 9091724069833602474660185)
                ·
                  refine ⟨6818793052375201855995139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9091724069833602474660185 6818793052375201855995139)
                  ·
                    refine ⟨10228189578562802783992709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6818793052375201855995139 10228189578562802783992709)
                    ·
                      refine ⟨1917785545980525521998633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10228189578562802783992709 1917785545980525521998633)
                      ·
                        rfl

theorem cell23_3734874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 3, 3, 2, 1, 4].length) (baseStart_3734874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3734874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3734874 prefixEnd_3734874 := by exact prefixLift 3734874
  have htrace : WordTrace (prefixWord ++ tailWord_3734874) baseStart_3734874 baseEnd_3734874 := by
    simpa [prefixWord, tailWord_3734874, baseEnd_3734874] using wordTrace_append hprefix tailTrace_3734874
  have hstable : (prefixWord ++ tailWord_3734874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3734874).length < 2 ^ (prefixWord ++ tailWord_3734874).sum := by decide
  have hdescent : baseEnd_3734874 < baseStart_3734874 := by decide
  rcases family_descends (prefixWord ++ tailWord_3734874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3734897 : List Nat := [1, 2, 2, 2, 1, 2, 2, 3, 8]
def baseStart_3734897 : Nat := 118140960795 + 3734897 * 2 ^ 59
def prefixEnd_3734897 : Nat := 4983230072969 + 3 ^ 40 * 3734897 * 2
def baseEnd_3734897 : Nat := 213088595115064325779003

theorem tailTrace_3734897 : CollatzResearch.WordTrace tailWord_3734897 prefixEnd_3734897 213088595115064325779003 := by
  unfold tailWord_3734897
  simp only [CollatzResearch.WordTrace]
  refine ⟨136222884750113513469314945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90815256500075675646209963 136222884750113513469314945)
  ·
    refine ⟨102167163562585135101986209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136222884750113513469314945 102167163562585135101986209)
    ·
      refine ⟨76625372671938851326489657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102167163562585135101986209 76625372671938851326489657)
      ·
        refine ⟨57469029503954138494867243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76625372671938851326489657 57469029503954138494867243)
        ·
          refine ⟨86203544255931207742300865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57469029503954138494867243 86203544255931207742300865)
          ·
            refine ⟨64652658191948405806725649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86203544255931207742300865 64652658191948405806725649)
            ·
              refine ⟨48489493643961304355044237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64652658191948405806725649 48489493643961304355044237)
              ·
                refine ⟨18183560116485489133141589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48489493643961304355044237 18183560116485489133141589)
                ·
                  refine ⟨213088595115064325779003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 18183560116485489133141589 213088595115064325779003)
                  ·
                    rfl

theorem cell23_3734897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 3, 8].length) (baseStart_3734897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3734897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3734897 prefixEnd_3734897 := by exact prefixLift 3734897
  have htrace : WordTrace (prefixWord ++ tailWord_3734897) baseStart_3734897 baseEnd_3734897 := by
    simpa [prefixWord, tailWord_3734897, baseEnd_3734897] using wordTrace_append hprefix tailTrace_3734897
  have hstable : (prefixWord ++ tailWord_3734897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3734897).length < 2 ^ (prefixWord ++ tailWord_3734897).sum := by decide
  have hdescent : baseEnd_3734897 < baseStart_3734897 := by decide
  rcases family_descends (prefixWord ++ tailWord_3734897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3734984 : List Nat := [2, 1, 3, 1, 3, 1, 1, 2, 3, 1, 5]
def baseStart_3734984 : Nat := 118140960795 + 3734984 * 2 ^ 59
def prefixEnd_3734984 : Nat := 4983230072969 + 3 ^ 40 * 3734984 * 2
def baseEnd_3734984 : Nat := 1917842028852520091623127

theorem tailTrace_3734984 : CollatzResearch.WordTrace tailWord_3734984 prefixEnd_3734984 1917842028852520091623127 := by
  unfold tailWord_3734984
  simp only [CollatzResearch.WordTrace]
  refine ⟨68113028950399163663866003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90817371933865551551821337 68113028950399163663866003)
  ·
    refine ⟨102169543425598745495799005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68113028950399163663866003 102169543425598745495799005)
    ·
      refine ⟨38313578784599529560924627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102169543425598745495799005 38313578784599529560924627)
      ·
        refine ⟨57470368176899294341386941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38313578784599529560924627 57470368176899294341386941)
        ·
          refine ⟨21551388066337235378020103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57470368176899294341386941 21551388066337235378020103)
          ·
            refine ⟨32327082099505853067030155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21551388066337235378020103 32327082099505853067030155)
            ·
              refine ⟨48490623149258779600545233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32327082099505853067030155 48490623149258779600545233)
              ·
                refine ⟨36367967361944084700408925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48490623149258779600545233 36367967361944084700408925)
                ·
                  refine ⟨13637987760729031762653347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36367967361944084700408925 13637987760729031762653347)
                  ·
                    refine ⟨20456981641093547643980021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13637987760729031762653347 20456981641093547643980021)
                    ·
                      refine ⟨1917842028852520091623127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20456981641093547643980021 1917842028852520091623127)
                      ·
                        rfl

theorem cell23_3734984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 2, 3, 1, 5].length) (baseStart_3734984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3734984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3734984 prefixEnd_3734984 := by exact prefixLift 3734984
  have htrace : WordTrace (prefixWord ++ tailWord_3734984) baseStart_3734984 baseEnd_3734984 := by
    simpa [prefixWord, tailWord_3734984, baseEnd_3734984] using wordTrace_append hprefix tailTrace_3734984
  have hstable : (prefixWord ++ tailWord_3734984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3734984).length < 2 ^ (prefixWord ++ tailWord_3734984).sum := by decide
  have hdescent : baseEnd_3734984 < baseStart_3734984 := by decide
  rcases family_descends (prefixWord ++ tailWord_3734984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3735001 : List Nat := [1, 2, 1, 2, 4, 3, 2, 1, 1, 1, 5]
def baseStart_3735001 : Nat := 118140960795 + 3735001 * 2 ^ 59
def prefixEnd_3735001 : Nat := 4983230072969 + 3 ^ 40 * 3735001 * 2
def baseEnd_3735001 : Nat := 1917850758023646525110549

theorem tailTrace_3735001 : CollatzResearch.WordTrace tailWord_3735001 prefixEnd_3735001 1917850758023646525110549 := by
  unfold tailWord_3735001
  simp only [CollatzResearch.WordTrace]
  refine ⟨136226677941736739231100857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90817785294491159487400571 136226677941736739231100857)
  ·
    refine ⟨102170008456302554423325643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136226677941736739231100857 102170008456302554423325643)
    ·
      refine ⟨153255012684453831634988465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102170008456302554423325643 153255012684453831634988465)
      ·
        refine ⟨114941259513340373726241349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 153255012684453831634988465 114941259513340373726241349)
        ·
          refine ⟨21551486158751320073670253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 114941259513340373726241349 21551486158751320073670253)
          ·
            refine ⟨8081807309531745027626345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21551486158751320073670253 8081807309531745027626345)
            ·
              refine ⟨6061355482148808770719759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8081807309531745027626345 6061355482148808770719759)
              ·
                refine ⟨9092033223223213156079639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6061355482148808770719759 9092033223223213156079639)
                ·
                  refine ⟨13638049834834819734119459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9092033223223213156079639 13638049834834819734119459)
                  ·
                    refine ⟨20457074752252229601179189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13638049834834819734119459 20457074752252229601179189)
                    ·
                      refine ⟨1917850758023646525110549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20457074752252229601179189 1917850758023646525110549)
                      ·
                        rfl

theorem cell23_3735001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 2, 1, 1, 1, 5].length) (baseStart_3735001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3735001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3735001 prefixEnd_3735001 := by exact prefixLift 3735001
  have htrace : WordTrace (prefixWord ++ tailWord_3735001) baseStart_3735001 baseEnd_3735001 := by
    simpa [prefixWord, tailWord_3735001, baseEnd_3735001] using wordTrace_append hprefix tailTrace_3735001
  have hstable : (prefixWord ++ tailWord_3735001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3735001).length < 2 ^ (prefixWord ++ tailWord_3735001).sum := by decide
  have hdescent : baseEnd_3735001 < baseStart_3735001 := by decide
  rcases family_descends (prefixWord ++ tailWord_3735001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3735015 : List Nat := [1, 1, 5, 2, 1, 2, 3, 1, 3, 2, 2]
def baseStart_3735015 : Nat := 118140960795 + 3735015 * 2 ^ 59
def prefixEnd_3735015 : Nat := 4983230072969 + 3 ^ 40 * 3735015 * 2
def baseEnd_3735015 : Nat := 1917857946752809470335485

theorem tailTrace_3735015 : CollatzResearch.WordTrace tailWord_3735015 prefixEnd_3735015 1917857946752809470335485 := by
  unfold tailWord_3735015
  simp only [CollatzResearch.WordTrace]
  refine ⟨136227188563686019622110499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90818125709124013081406999 136227188563686019622110499)
  ·
    refine ⟨204340782845529029433165749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136227188563686019622110499 204340782845529029433165749)
    ·
      refine ⟨19156948391768346509359289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 204340782845529029433165749 19156948391768346509359289)
      ·
        refine ⟨14367711293826259882019467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19156948391768346509359289 14367711293826259882019467)
        ·
          refine ⟨21551566940739389823029201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14367711293826259882019467 21551566940739389823029201)
          ·
            refine ⟨16163675205554542367271901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21551566940739389823029201 16163675205554542367271901)
            ·
              refine ⟨6061378202082953387726963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16163675205554542367271901 6061378202082953387726963)
              ·
                refine ⟨9092067303124430081590445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6061378202082953387726963 9092067303124430081590445)
                ·
                  refine ⟨3409525238671661280596417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9092067303124430081590445 3409525238671661280596417)
                  ·
                    refine ⟨2557143929003745960447313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3409525238671661280596417 2557143929003745960447313)
                    ·
                      refine ⟨1917857946752809470335485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2557143929003745960447313 1917857946752809470335485)
                      ·
                        rfl

theorem cell23_3735015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 3, 1, 3, 2, 2].length) (baseStart_3735015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3735015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3735015 prefixEnd_3735015 := by exact prefixLift 3735015
  have htrace : WordTrace (prefixWord ++ tailWord_3735015) baseStart_3735015 baseEnd_3735015 := by
    simpa [prefixWord, tailWord_3735015, baseEnd_3735015] using wordTrace_append hprefix tailTrace_3735015
  have hstable : (prefixWord ++ tailWord_3735015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3735015).length < 2 ^ (prefixWord ++ tailWord_3735015).sum := by decide
  have hdescent : baseEnd_3735015 < baseStart_3735015 := by decide
  rcases family_descends (prefixWord ++ tailWord_3735015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3735025 : List Nat := [1, 2, 2, 2, 3, 4, 2, 1, 2, 4]
def baseStart_3735025 : Nat := 118140960795 + 3735025 * 2 ^ 59
def prefixEnd_3735025 : Nat := 4983230072969 + 3 ^ 40 * 3735025 * 2
def baseEnd_3735025 : Nat := 639287693853118143736813

theorem tailTrace_3735025 : CollatzResearch.WordTrace tailWord_3735025 prefixEnd_3735025 639287693853118143736813 := by
  unfold tailWord_3735025
  simp only [CollatzResearch.WordTrace]
  refine ⟨136227553293649791329974529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90818368862433194219983019 136227553293649791329974529)
  ·
    refine ⟨102170664970237343497480897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136227553293649791329974529 102170664970237343497480897)
    ·
      refine ⟨76627998727678007623110673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102170664970237343497480897 76627998727678007623110673)
      ·
        refine ⟨57470999045758505717333005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76627998727678007623110673 57470999045758505717333005)
        ·
          refine ⟨21551624642159439643999877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57470999045758505717333005 21551624642159439643999877)
          ·
            refine ⟨4040929620404894933249977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21551624642159439643999877 4040929620404894933249977)
            ·
              refine ⟨3030697215303671199937483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4040929620404894933249977 3030697215303671199937483)
              ·
                refine ⟨4546045822955506799906225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3030697215303671199937483 4546045822955506799906225)
                ·
                  refine ⟨3409534367216630099929669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4546045822955506799906225 3409534367216630099929669)
                  ·
                    refine ⟨639287693853118143736813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3409534367216630099929669 639287693853118143736813)
                    ·
                      rfl

theorem cell23_3735025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 4, 2, 1, 2, 4].length) (baseStart_3735025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3735025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3735025 prefixEnd_3735025 := by exact prefixLift 3735025
  have htrace : WordTrace (prefixWord ++ tailWord_3735025) baseStart_3735025 baseEnd_3735025 := by
    simpa [prefixWord, tailWord_3735025, baseEnd_3735025] using wordTrace_append hprefix tailTrace_3735025
  have hstable : (prefixWord ++ tailWord_3735025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3735025).length < 2 ^ (prefixWord ++ tailWord_3735025).sum := by decide
  have hdescent : baseEnd_3735025 < baseStart_3735025 := by decide
  rcases family_descends (prefixWord ++ tailWord_3735025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3735031 : List Nat := [1, 1, 3, 1, 1, 1, 1, 4, 6, 1, 3]
def baseStart_3735031 : Nat := 118140960795 + 3735031 * 2 ^ 59
def prefixEnd_3735031 : Nat := 4983230072969 + 3 ^ 40 * 3735031 * 2
def baseEnd_3735031 : Nat := 1917866162443281407735411

theorem tailTrace_3735031 : CollatzResearch.WordTrace tailWord_3735031 prefixEnd_3735031 1917866162443281407735411 := by
  unfold tailWord_3735031
  simp only [CollatzResearch.WordTrace]
  refine ⟨136227772131628054354692947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90818514754418702903128631 136227772131628054354692947)
  ·
    refine ⟨204341658197442081532039421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136227772131628054354692947 204341658197442081532039421)
    ·
      refine ⟨76628121824040780574514783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 204341658197442081532039421 76628121824040780574514783)
      ·
        refine ⟨114942182736061170861772175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76628121824040780574514783 114942182736061170861772175)
        ·
          refine ⟨172413274104091756292658263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114942182736061170861772175 172413274104091756292658263)
          ·
            refine ⟨258619911156137634438987395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 172413274104091756292658263 258619911156137634438987395)
            ·
              refine ⟨387929866734206451658481093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 258619911156137634438987395 387929866734206451658481093)
              ·
                refine ⟨72736850012663709685965205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 387929866734206451658481093 72736850012663709685965205)
                ·
                  refine ⟨3409539844343611391529619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 72736850012663709685965205 3409539844343611391529619)
                  ·
                    refine ⟨5114309766515417087294429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3409539844343611391529619 5114309766515417087294429)
                    ·
                      refine ⟨1917866162443281407735411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5114309766515417087294429 1917866162443281407735411)
                      ·
                        rfl

theorem cell23_3735031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 4, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 4, 6, 1, 3].length) (baseStart_3735031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3735031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3735031 prefixEnd_3735031 := by exact prefixLift 3735031
  have htrace : WordTrace (prefixWord ++ tailWord_3735031) baseStart_3735031 baseEnd_3735031 := by
    simpa [prefixWord, tailWord_3735031, baseEnd_3735031] using wordTrace_append hprefix tailTrace_3735031
  have hstable : (prefixWord ++ tailWord_3735031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3735031).length < 2 ^ (prefixWord ++ tailWord_3735031).sum := by decide
  have hdescent : baseEnd_3735031 < baseStart_3735031 := by decide
  rcases family_descends (prefixWord ++ tailWord_3735031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3735088 : List Nat := [2, 1, 1, 1, 2, 3, 1, 2, 6, 2, 2]
def baseStart_3735088 : Nat := 118140960795 + 3735088 * 2 ^ 59
def prefixEnd_3735088 : Nat := 4983230072969 + 3 ^ 40 * 3735088 * 2
def baseEnd_3735088 : Nat := 1917895430840587684722649

theorem tailTrace_3735088 : CollatzResearch.WordTrace tailWord_3735088 prefixEnd_3735088 1917895430840587684722649 := by
  unfold tailWord_3735088
  simp only [CollatzResearch.WordTrace]
  refine ⟨68114925546210776544758959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90819900728281035393011945 68114925546210776544758959)
  ·
    refine ⟨102172388319316164817138439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68114925546210776544758959 102172388319316164817138439)
    ·
      refine ⟨153258582478974247225707659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102172388319316164817138439 153258582478974247225707659)
      ·
        refine ⟨229887873718461370838561489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153258582478974247225707659 229887873718461370838561489)
        ·
          refine ⟨172415905288846028128921117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 229887873718461370838561489 172415905288846028128921117)
          ·
            refine ⟨64655964483317260548345419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 172415905288846028128921117 64655964483317260548345419)
            ·
              refine ⟨96983946724975890822518129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64655964483317260548345419 96983946724975890822518129)
              ·
                refine ⟨72737960043731918116888597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 96983946724975890822518129 72737960043731918116888597)
                ·
                  refine ⟨3409591877049933661729153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 72737960043731918116888597 3409591877049933661729153)
                  ·
                    refine ⟨2557193907787450246296865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3409591877049933661729153 2557193907787450246296865)
                    ·
                      refine ⟨1917895430840587684722649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2557193907787450246296865 1917895430840587684722649)
                      ·
                        rfl

theorem cell23_3735088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 2, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 2, 6, 2, 2].length) (baseStart_3735088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3735088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3735088 prefixEnd_3735088 := by exact prefixLift 3735088
  have htrace : WordTrace (prefixWord ++ tailWord_3735088) baseStart_3735088 baseEnd_3735088 := by
    simpa [prefixWord, tailWord_3735088, baseEnd_3735088] using wordTrace_append hprefix tailTrace_3735088
  have hstable : (prefixWord ++ tailWord_3735088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3735088).length < 2 ^ (prefixWord ++ tailWord_3735088).sum := by decide
  have hdescent : baseEnd_3735088 < baseStart_3735088 := by decide
  rcases family_descends (prefixWord ++ tailWord_3735088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3735104 : List Nat := [2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 7]
def baseStart_3735104 : Nat := 118140960795 + 3735104 * 2 ^ 59
def prefixEnd_3735104 : Nat := 4983230072969 + 3 ^ 40 * 3735104 * 2
def baseEnd_3735104 : Nat := 1917903646531059622122575

theorem tailTrace_3735104 : CollatzResearch.WordTrace tailWord_3735104 prefixEnd_3735104 1917903646531059622122575 := by
  unfold tailWord_3735104
  simp only [CollatzResearch.WordTrace]
  refine ⟨68115217330181793911050183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90820289773575725214733577 68115217330181793911050183)
  ·
    refine ⟨102172825995272690866575275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68115217330181793911050183 102172825995272690866575275)
    ·
      refine ⟨153259238992909036299862913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102172825995272690866575275 153259238992909036299862913)
      ·
        refine ⟨114944429244681777224897185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 153259238992909036299862913 114944429244681777224897185)
        ·
          refine ⟨86208321933511332918672889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114944429244681777224897185 86208321933511332918672889)
          ·
            refine ⟨64656241450133499689004667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86208321933511332918672889 64656241450133499689004667)
            ·
              refine ⟨96984362175200249533507001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64656241450133499689004667 96984362175200249533507001)
              ·
                refine ⟨72738271631400187150130251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 96984362175200249533507001 72738271631400187150130251)
                ·
                  refine ⟨109107407447100280725195377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 72738271631400187150130251 109107407447100280725195377)
                  ·
                    refine ⟨81830555585325210543896533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 109107407447100280725195377 81830555585325210543896533)
                    ·
                      refine ⟨1917903646531059622122575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 81830555585325210543896533 1917903646531059622122575)
                      ·
                        rfl

theorem cell23_3735104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 7].length) (baseStart_3735104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3735104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3735104 prefixEnd_3735104 := by exact prefixLift 3735104
  have htrace : WordTrace (prefixWord ++ tailWord_3735104) baseStart_3735104 baseEnd_3735104 := by
    simpa [prefixWord, tailWord_3735104, baseEnd_3735104] using wordTrace_append hprefix tailTrace_3735104
  have hstable : (prefixWord ++ tailWord_3735104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3735104).length < 2 ^ (prefixWord ++ tailWord_3735104).sum := by decide
  have hdescent : baseEnd_3735104 < baseStart_3735104 := by decide
  rcases family_descends (prefixWord ++ tailWord_3735104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3735105 : List Nat := [1, 2, 5, 1, 1, 1, 2, 2, 4, 2, 2]
def baseStart_3735105 : Nat := 118140960795 + 3735105 * 2 ^ 59
def prefixEnd_3735105 : Nat := 4983230072969 + 3 ^ 40 * 3735105 * 2
def baseEnd_3735105 : Nat := 1917904160011714118210071

theorem tailTrace_3735105 : CollatzResearch.WordTrace tailWord_3735105 prefixEnd_3735105 1917904160011714118210071 := by
  unfold tailWord_3735105
  simp only [CollatzResearch.WordTrace]
  refine ⟨136230471133359964992886769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90820314088906643328591179 136230471133359964992886769)
  ·
    refine ⟨102172853350019973744665077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136230471133359964992886769 102172853350019973744665077)
    ·
      refine ⟨9578705001564372538562351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 102172853350019973744665077 9578705001564372538562351)
      ·
        refine ⟨14368057502346558807843527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9578705001564372538562351 14368057502346558807843527)
        ·
          refine ⟨21552086253519838211765291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14368057502346558807843527 21552086253519838211765291)
          ·
            refine ⟨32328129380279757317647937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21552086253519838211765291 32328129380279757317647937)
            ·
              refine ⟨24246097035209817988235953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32328129380279757317647937 24246097035209817988235953)
              ·
                refine ⟨18184572776407363491176965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24246097035209817988235953 18184572776407363491176965)
                ·
                  refine ⟨3409607395576380654595681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18184572776407363491176965 3409607395576380654595681)
                  ·
                    refine ⟨2557205546682285490946761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3409607395576380654595681 2557205546682285490946761)
                    ·
                      refine ⟨1917904160011714118210071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2557205546682285490946761 1917904160011714118210071)
                      ·
                        rfl

theorem cell23_3735105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 2, 2, 4, 2, 2].length) (baseStart_3735105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3735105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3735105 prefixEnd_3735105 := by exact prefixLift 3735105
  have htrace : WordTrace (prefixWord ++ tailWord_3735105) baseStart_3735105 baseEnd_3735105 := by
    simpa [prefixWord, tailWord_3735105, baseEnd_3735105] using wordTrace_append hprefix tailTrace_3735105
  have hstable : (prefixWord ++ tailWord_3735105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3735105).length < 2 ^ (prefixWord ++ tailWord_3735105).sum := by decide
  have hdescent : baseEnd_3735105 < baseStart_3735105 := by decide
  rcases family_descends (prefixWord ++ tailWord_3735105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3735121 : List Nat := [1, 2, 2, 1, 3, 2, 1, 1, 4, 3, 3]
def baseStart_3735121 : Nat := 118140960795 + 3735121 * 2 ^ 59
def prefixEnd_3735121 : Nat := 4983230072969 + 3 ^ 40 * 3735121 * 2
def baseEnd_3735121 : Nat := 1917912375702186055609997

theorem tailTrace_3735121 : CollatzResearch.WordTrace tailWord_3735121 prefixEnd_3735121 1917912375702186055609997 := by
  unfold tailWord_3735121
  simp only [CollatzResearch.WordTrace]
  refine ⟨136231054701301999725469217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90820703134201333150312811 136231054701301999725469217)
  ·
    refine ⟨102173291025976499794101913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136231054701301999725469217 102173291025976499794101913)
    ·
      refine ⟨76629968269482374845576435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102173291025976499794101913 76629968269482374845576435)
      ·
        refine ⟨114944952404223562268364653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76629968269482374845576435 114944952404223562268364653)
        ·
          refine ⟨43104357151583835850636745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 114944952404223562268364653 43104357151583835850636745)
          ·
            refine ⟨32328267863687876887977559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43104357151583835850636745 32328267863687876887977559)
            ·
              refine ⟨48492401795531815331966339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32328267863687876887977559 48492401795531815331966339)
              ·
                refine ⟨72738602693297722997949509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48492401795531815331966339 72738602693297722997949509)
                ·
                  refine ⟨13638488004993323062115533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 72738602693297722997949509 13638488004993323062115533)
                  ·
                    refine ⟨5114433001872496148293325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13638488004993323062115533 5114433001872496148293325)
                    ·
                      refine ⟨1917912375702186055609997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5114433001872496148293325 1917912375702186055609997)
                      ·
                        rfl

theorem cell23_3735121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 1, 4, 3, 3].length) (baseStart_3735121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3735121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3735121 prefixEnd_3735121 := by exact prefixLift 3735121
  have htrace : WordTrace (prefixWord ++ tailWord_3735121) baseStart_3735121 baseEnd_3735121 := by
    simpa [prefixWord, tailWord_3735121, baseEnd_3735121] using wordTrace_append hprefix tailTrace_3735121
  have hstable : (prefixWord ++ tailWord_3735121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3735121).length < 2 ^ (prefixWord ++ tailWord_3735121).sum := by decide
  have hdescent : baseEnd_3735121 < baseStart_3735121 := by decide
  rcases family_descends (prefixWord ++ tailWord_3735121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3735122 : List Nat := [3, 2, 2, 1, 2, 2, 3, 2, 2, 2, 2]
def baseStart_3735122 : Nat := 118140960795 + 3735122 * 2 ^ 59
def prefixEnd_3735122 : Nat := 4983230072969 + 3 ^ 40 * 3735122 * 2
def baseEnd_3735122 : Nat := 1917912889182840551697493

theorem tailTrace_3735122 : CollatzResearch.WordTrace tailWord_3735122 prefixEnd_3735122 1917912889182840551697493 := by
  unfold tailWord_3735122
  simp only [CollatzResearch.WordTrace]
  refine ⟨34057772793574594224063905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90820727449532251264170413 34057772793574594224063905)
  ·
    refine ⟨25543329595180945668047929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34057772793574594224063905 25543329595180945668047929)
    ·
      refine ⟨19157497196385709251035947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25543329595180945668047929 19157497196385709251035947)
      ·
        refine ⟨28736245794578563876553921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19157497196385709251035947 28736245794578563876553921)
        ·
          refine ⟨21552184345933922907415441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28736245794578563876553921 21552184345933922907415441)
          ·
            refine ⟨16164138259450442180561581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21552184345933922907415441 16164138259450442180561581)
            ·
              refine ⟨6061551847293915817710593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16164138259450442180561581 6061551847293915817710593)
              ·
                refine ⟨4546163885470436863282945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6061551847293915817710593 4546163885470436863282945)
                ·
                  refine ⟨3409622914102827647462209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4546163885470436863282945 3409622914102827647462209)
                  ·
                    refine ⟨2557217185577120735596657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3409622914102827647462209 2557217185577120735596657)
                    ·
                      refine ⟨1917912889182840551697493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2557217185577120735596657 1917912889182840551697493)
                      ·
                        rfl

theorem cell23_3735122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 3, 2, 2, 2, 2].length) (baseStart_3735122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3735122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3735122 prefixEnd_3735122 := by exact prefixLift 3735122
  have htrace : WordTrace (prefixWord ++ tailWord_3735122) baseStart_3735122 baseEnd_3735122 := by
    simpa [prefixWord, tailWord_3735122, baseEnd_3735122] using wordTrace_append hprefix tailTrace_3735122
  have hstable : (prefixWord ++ tailWord_3735122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3735122).length < 2 ^ (prefixWord ++ tailWord_3735122).sum := by decide
  have hdescent : baseEnd_3735122 < baseStart_3735122 := by decide
  rcases family_descends (prefixWord ++ tailWord_3735122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3735141 : List Nat := [1, 3, 1, 3, 3, 1, 1, 2, 1, 7]
def baseStart_3735141 : Nat := 118140960795 + 3735141 * 2 ^ 59
def prefixEnd_3735141 : Nat := 4983230072969 + 3 ^ 40 * 3735141 * 2
def baseEnd_3735141 : Nat := 639307548438425325786635

theorem tailTrace_3735141 : CollatzResearch.WordTrace tailWord_3735141 prefixEnd_3735141 639307548438425325786635 := by
  unfold tailWord_3735141
  simp only [CollatzResearch.WordTrace]
  refine ⟨136231784161229543141197277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90821189440819695427464851 136231784161229543141197277)
  ·
    refine ⟨51086919060461078677948979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 136231784161229543141197277 51086919060461078677948979)
    ·
      refine ⟨76630378590691618016923469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51086919060461078677948979 76630378590691618016923469)
      ·
        refine ⟨28736391971509356756346301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76630378590691618016923469 28736391971509356756346301)
        ·
          refine ⟨10776146989316008783629863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28736391971509356756346301 10776146989316008783629863)
          ·
            refine ⟨16164220483974013175444795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10776146989316008783629863 16164220483974013175444795)
            ·
              refine ⟨24246330725961019763167193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16164220483974013175444795 24246330725961019763167193)
              ·
                refine ⟨18184748044470764822375395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24246330725961019763167193 18184748044470764822375395)
                ·
                  refine ⟨27277122066706147233563093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18184748044470764822375395 27277122066706147233563093)
                  ·
                    refine ⟨639307548438425325786635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 27277122066706147233563093 639307548438425325786635)
                    ·
                      rfl

theorem cell23_3735141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 1, 2, 1, 7].length) (baseStart_3735141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3735141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3735141 prefixEnd_3735141 := by exact prefixLift 3735141
  have htrace : WordTrace (prefixWord ++ tailWord_3735141) baseStart_3735141 baseEnd_3735141 := by
    simpa [prefixWord, tailWord_3735141, baseEnd_3735141] using wordTrace_append hprefix tailTrace_3735141
  have hstable : (prefixWord ++ tailWord_3735141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3735141).length < 2 ^ (prefixWord ++ tailWord_3735141).sum := by decide
  have hdescent : baseEnd_3735141 < baseStart_3735141 := by decide
  rcases family_descends (prefixWord ++ tailWord_3735141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3735158 : List Nat := [5, 1, 1, 2, 2, 1, 2, 1, 1, 7]
def baseStart_3735158 : Nat := 118140960795 + 3735158 * 2 ^ 59
def prefixEnd_3735158 : Nat := 4983230072969 + 3 ^ 40 * 3735158 * 2
def baseEnd_3735158 : Nat := 639310458162134136949109

theorem tailTrace_3735158 : CollatzResearch.WordTrace tailWord_3735158 prefixEnd_3735158 639310458162134136949109 := by
  unfold tailWord_3735158
  simp only [CollatzResearch.WordTrace]
  refine ⟨8514525262635497190285383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 90821602801445303363044085 8514525262635497190285383)
  ·
    refine ⟨12771787893953245785428075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8514525262635497190285383 12771787893953245785428075)
    ·
      refine ⟨19157681840929868678142113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12771787893953245785428075 19157681840929868678142113)
      ·
        refine ⟨14368261380697401508606585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19157681840929868678142113 14368261380697401508606585)
        ·
          refine ⟨10776196035523051131454939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14368261380697401508606585 10776196035523051131454939)
          ·
            refine ⟨16164294053284576697182409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10776196035523051131454939 16164294053284576697182409)
            ·
              refine ⟨12123220539963432522886807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16164294053284576697182409 12123220539963432522886807)
              ·
                refine ⟨18184830809945148784330211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12123220539963432522886807 18184830809945148784330211)
                ·
                  refine ⟨27277246214917723176495317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18184830809945148784330211 27277246214917723176495317)
                  ·
                    refine ⟨639310458162134136949109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 27277246214917723176495317 639310458162134136949109)
                    ·
                      rfl

theorem cell23_3735158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 2, 1, 1, 7].length) (baseStart_3735158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3735158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3735158 prefixEnd_3735158 := by exact prefixLift 3735158
  have htrace : WordTrace (prefixWord ++ tailWord_3735158) baseStart_3735158 baseEnd_3735158 := by
    simpa [prefixWord, tailWord_3735158, baseEnd_3735158] using wordTrace_append hprefix tailTrace_3735158
  have hstable : (prefixWord ++ tailWord_3735158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3735158).length < 2 ^ (prefixWord ++ tailWord_3735158).sum := by decide
  have hdescent : baseEnd_3735158 < baseStart_3735158 := by decide
  rcases family_descends (prefixWord ++ tailWord_3735158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3735161 : List Nat := [1, 2, 1, 3, 3, 1, 1, 3, 1, 3, 4]
def baseStart_3735161 : Nat := 118140960795 + 3735161 * 2 ^ 59
def prefixEnd_3735161 : Nat := 4983230072969 + 3 ^ 40 * 3735161 * 2
def baseEnd_3735161 : Nat := 1917932914928365899109813

theorem tailTrace_3735161 : CollatzResearch.WordTrace tailWord_3735161 prefixEnd_3735161 1917932914928365899109813 := by
  unfold tailWord_3735161
  simp only [CollatzResearch.WordTrace]
  refine ⟨136232513621157086556925337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90821675747438057704616891 136232513621157086556925337)
  ·
    refine ⟨102174385215867814917694003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136232513621157086556925337 102174385215867814917694003)
    ·
      refine ⟨153261577823801722376541005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102174385215867814917694003 153261577823801722376541005)
      ·
        refine ⟨57473091683925645891202877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 153261577823801722376541005 57473091683925645891202877)
        ·
          refine ⟨21552409381472117209201079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57473091683925645891202877 21552409381472117209201079)
          ·
            refine ⟨32328614072208175813801619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21552409381472117209201079 32328614072208175813801619)
            ·
              refine ⟨48492921108312263720702429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32328614072208175813801619 48492921108312263720702429)
              ·
                refine ⟨18184845415617098895263411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48492921108312263720702429 18184845415617098895263411)
                ·
                  refine ⟨27277268123425648342895117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18184845415617098895263411 27277268123425648342895117)
                  ·
                    refine ⟨10228975546284618128585669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27277268123425648342895117 10228975546284618128585669)
                    ·
                      refine ⟨1917932914928365899109813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10228975546284618128585669 1917932914928365899109813)
                      ·
                        rfl

theorem cell23_3735161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 3, 1, 3, 4].length) (baseStart_3735161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3735161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3735161 prefixEnd_3735161 := by exact prefixLift 3735161
  have htrace : WordTrace (prefixWord ++ tailWord_3735161) baseStart_3735161 baseEnd_3735161 := by
    simpa [prefixWord, tailWord_3735161, baseEnd_3735161] using wordTrace_append hprefix tailTrace_3735161
  have hstable : (prefixWord ++ tailWord_3735161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3735161).length < 2 ^ (prefixWord ++ tailWord_3735161).sum := by decide
  have hdescent : baseEnd_3735161 < baseStart_3735161 := by decide
  rcases family_descends (prefixWord ++ tailWord_3735161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3735178 : List Nat := [3, 1, 2, 3, 2, 1, 1, 1, 4, 1, 4]
def baseStart_3735178 : Nat := 118140960795 + 3735178 * 2 ^ 59
def prefixEnd_3735178 : Nat := 4983230072969 + 3 ^ 40 * 3735178 * 2
def baseEnd_3735178 : Nat := 1917941644099492332597235

theorem tailTrace_3735178 : CollatzResearch.WordTrace tailWord_3735178 prefixEnd_3735178 1917941644099492332597235 := by
  unfold tailWord_3735178
  simp only [CollatzResearch.WordTrace]
  refine ⟨34058283415523874615073547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90822089108063665640196125 34058283415523874615073547)
  ·
    refine ⟨51087425123285811922610321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34058283415523874615073547 51087425123285811922610321)
    ·
      refine ⟨38315568842464358941957741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51087425123285811922610321 38315568842464358941957741)
      ·
        refine ⟨14368338315924134603234153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38315568842464358941957741 14368338315924134603234153)
        ·
          refine ⟨10776253736943100952425615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14368338315924134603234153 10776253736943100952425615)
          ·
            refine ⟨16164380605414651428638423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10776253736943100952425615 16164380605414651428638423)
            ·
              refine ⟨24246570908121977142957635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16164380605414651428638423 24246570908121977142957635)
              ·
                refine ⟨36369856362182965714436453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24246570908121977142957635 36369856362182965714436453)
                ·
                  refine ⟨6819348067909306071456835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36369856362182965714436453 6819348067909306071456835)
                  ·
                    refine ⟨10229022101863959107185253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6819348067909306071456835 10229022101863959107185253)
                    ·
                      refine ⟨1917941644099492332597235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10229022101863959107185253 1917941644099492332597235)
                      ·
                        rfl

theorem cell23_3735178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 1, 1, 4, 1, 4].length) (baseStart_3735178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3735178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3735178 prefixEnd_3735178 := by exact prefixLift 3735178
  have htrace : WordTrace (prefixWord ++ tailWord_3735178) baseStart_3735178 baseEnd_3735178 := by
    simpa [prefixWord, tailWord_3735178, baseEnd_3735178] using wordTrace_append hprefix tailTrace_3735178
  have hstable : (prefixWord ++ tailWord_3735178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3735178).length < 2 ^ (prefixWord ++ tailWord_3735178).sum := by decide
  have hdescent : baseEnd_3735178 < baseStart_3735178 := by decide
  rcases family_descends (prefixWord ++ tailWord_3735178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3735268 : List Nat := [2, 3, 1, 1, 1, 3, 1, 3, 3, 1, 4]
def baseStart_3735268 : Nat := 118140960795 + 3735268 * 2 ^ 59
def prefixEnd_3735268 : Nat := 4983230072969 + 3 ^ 40 * 3735268 * 2
def baseEnd_3735268 : Nat := 1917987857358396980471821

theorem tailTrace_3735268 : CollatzResearch.WordTrace tailWord_3735268 prefixEnd_3735268 1917987857358396980471821 := by
  unfold tailWord_3735268
  simp only [CollatzResearch.WordTrace]
  refine ⟨68118208115884721915535229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90824277487846295887380305 68118208115884721915535229)
  ·
    refine ⟨25544328043456770718325711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68118208115884721915535229 25544328043456770718325711)
    ·
      refine ⟨38316492065185156077488567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25544328043456770718325711 38316492065185156077488567)
      ·
        refine ⟨57474738097777734116232851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38316492065185156077488567 57474738097777734116232851)
        ·
          refine ⟨86212107146666601174349277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57474738097777734116232851 86212107146666601174349277)
          ·
            refine ⟨32329540179999975440380979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 86212107146666601174349277 32329540179999975440380979)
            ·
              refine ⟨48494310269999963160571469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32329540179999975440380979 48494310269999963160571469)
              ·
                refine ⟨18185366351249986185214301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48494310269999963160571469 18185366351249986185214301)
                ·
                  refine ⟨6819512381718744819455363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18185366351249986185214301 6819512381718744819455363)
                  ·
                    refine ⟨10229268572578117229183045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6819512381718744819455363 10229268572578117229183045)
                    ·
                      refine ⟨1917987857358396980471821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10229268572578117229183045 1917987857358396980471821)
                      ·
                        rfl

theorem cell23_3735268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 3, 3, 1, 4].length) (baseStart_3735268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3735268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3735268 prefixEnd_3735268 := by exact prefixLift 3735268
  have htrace : WordTrace (prefixWord ++ tailWord_3735268) baseStart_3735268 baseEnd_3735268 := by
    simpa [prefixWord, tailWord_3735268, baseEnd_3735268] using wordTrace_append hprefix tailTrace_3735268
  have hstable : (prefixWord ++ tailWord_3735268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3735268).length < 2 ^ (prefixWord ++ tailWord_3735268).sum := by decide
  have hdescent : baseEnd_3735268 < baseStart_3735268 := by decide
  rcases family_descends (prefixWord ++ tailWord_3735268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3735272 : List Nat := [2, 1, 4, 1, 3, 1, 3, 1, 2, 3, 2]
def baseStart_3735272 : Nat := 118140960795 + 3735272 * 2 ^ 59
def prefixEnd_3735272 : Nat := 4983230072969 + 3 ^ 40 * 3735272 * 2
def baseEnd_3735272 : Nat := 1917989911281014964821803

theorem tailTrace_3735272 : CollatzResearch.WordTrace tailWord_3735272 prefixEnd_3735272 1917989911281014964821803 := by
  unfold tailWord_3735272
  simp only [CollatzResearch.WordTrace]
  refine ⟨68118281061877476257108035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90824374749169968342810713 68118281061877476257108035)
  ·
    refine ⟨102177421592816214385662053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68118281061877476257108035 102177421592816214385662053)
    ·
      refine ⟨19158266548653040197311635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 102177421592816214385662053 19158266548653040197311635)
      ·
        refine ⟨28737399822979560295967453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19158266548653040197311635 28737399822979560295967453)
        ·
          refine ⟨10776524933617335110987795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28737399822979560295967453 10776524933617335110987795)
          ·
            refine ⟨16164787400426002666481693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10776524933617335110987795 16164787400426002666481693)
            ·
              refine ⟨6061795275159750999930635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16164787400426002666481693 6061795275159750999930635)
              ·
                refine ⟨9092692912739626499895953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6061795275159750999930635 9092692912739626499895953)
                ·
                  refine ⟨6819519684554719874921965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9092692912739626499895953 6819519684554719874921965)
                  ·
                    refine ⟨2557319881708019953095737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6819519684554719874921965 2557319881708019953095737)
                    ·
                      refine ⟨1917989911281014964821803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2557319881708019953095737 1917989911281014964821803)
                      ·
                        rfl

theorem cell23_3735272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 3, 1, 2, 3, 2].length) (baseStart_3735272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3735272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3735272 prefixEnd_3735272 := by exact prefixLift 3735272
  have htrace : WordTrace (prefixWord ++ tailWord_3735272) baseStart_3735272 baseEnd_3735272 := by
    simpa [prefixWord, tailWord_3735272, baseEnd_3735272] using wordTrace_append hprefix tailTrace_3735272
  have hstable : (prefixWord ++ tailWord_3735272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3735272).length < 2 ^ (prefixWord ++ tailWord_3735272).sum := by decide
  have hdescent : baseEnd_3735272 < baseStart_3735272 := by decide
  rcases family_descends (prefixWord ++ tailWord_3735272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3735278 : List Nat := [4, 1, 2, 1, 1, 2, 1, 4, 1, 6]
def baseStart_3735278 : Nat := 118140960795 + 3735278 * 2 ^ 59
def prefixEnd_3735278 : Nat := 4983230072969 + 3 ^ 40 * 3735278 * 2
def baseEnd_3735278 : Nat := 639330997388313980448925

theorem tailTrace_3735278 : CollatzResearch.WordTrace tailWord_3735278 prefixEnd_3735278 639330997388313980448925 := by
  unfold tailWord_3735278
  simp only [CollatzResearch.WordTrace]
  refine ⟨17029597620216651942366811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 90824520641155477025956325 17029597620216651942366811)
  ·
    refine ⟨25544396430324977913550217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17029597620216651942366811 25544396430324977913550217)
    ·
      refine ⟨19158297322743733435162663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25544396430324977913550217 19158297322743733435162663)
      ·
        refine ⟨28737445984115600152743995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19158297322743733435162663 28737445984115600152743995)
        ·
          refine ⟨43106168976173400229115993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28737445984115600152743995 43106168976173400229115993)
          ·
            refine ⟨32329626732130050171836995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43106168976173400229115993 32329626732130050171836995)
            ·
              refine ⟨48494440098195075257755493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32329626732130050171836995 48494440098195075257755493)
              ·
                refine ⟨9092707518411576610829155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48494440098195075257755493 9092707518411576610829155)
                ·
                  refine ⟨13639061277617364916243733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9092707518411576610829155 13639061277617364916243733)
                  ·
                    refine ⟨639330997388313980448925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13639061277617364916243733 639330997388313980448925)
                    ·
                      rfl

theorem cell23_3735278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 4, 1, 6].length) (baseStart_3735278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3735278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3735278 prefixEnd_3735278 := by exact prefixLift 3735278
  have htrace : WordTrace (prefixWord ++ tailWord_3735278) baseStart_3735278 baseEnd_3735278 := by
    simpa [prefixWord, tailWord_3735278, baseEnd_3735278] using wordTrace_append hprefix tailTrace_3735278
  have hstable : (prefixWord ++ tailWord_3735278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3735278).length < 2 ^ (prefixWord ++ tailWord_3735278).sum := by decide
  have hdescent : baseEnd_3735278 < baseStart_3735278 := by decide
  rcases family_descends (prefixWord ++ tailWord_3735278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3735288 : List Nat := [2, 1, 2, 1, 1, 2, 2, 2, 5, 2, 3]
def baseStart_3735288 : Nat := 118140960795 + 3735288 * 2 ^ 59
def prefixEnd_3735288 : Nat := 4983230072969 + 3 ^ 40 * 3735288 * 2
def baseEnd_3735288 : Nat := 1917998126971486902221729

theorem tailTrace_3735288 : CollatzResearch.WordTrace tailWord_3735288 prefixEnd_3735288 1917998126971486902221729 := by
  unfold tailWord_3735288
  simp only [CollatzResearch.WordTrace]
  refine ⟨68118572845848493623399259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90824763794464658164532345 68118572845848493623399259)
  ·
    refine ⟨102177859268772740435098889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68118572845848493623399259 102177859268772740435098889)
    ·
      refine ⟨76633394451579555326324167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102177859268772740435098889 76633394451579555326324167)
      ·
        refine ⟨114950091677369332989486251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76633394451579555326324167 114950091677369332989486251)
        ·
          refine ⟨172425137516053999484229377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114950091677369332989486251 172425137516053999484229377)
          ·
            refine ⟨129318853137040499613172033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 172425137516053999484229377 129318853137040499613172033)
            ·
              refine ⟨96989139852780374709879025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 129318853137040499613172033 96989139852780374709879025)
              ·
                refine ⟨72741854889585281032409269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 96989139852780374709879025 72741854889585281032409269)
                ·
                  refine ⟨6819548895898620096788369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 72741854889585281032409269 6819548895898620096788369)
                  ·
                    refine ⟨5114661671923965072591277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6819548895898620096788369 5114661671923965072591277)
                    ·
                      refine ⟨1917998126971486902221729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5114661671923965072591277 1917998126971486902221729)
                      ·
                        rfl

theorem cell23_3735288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 2, 5, 2, 3].length) (baseStart_3735288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3735288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3735288 prefixEnd_3735288 := by exact prefixLift 3735288
  have htrace : WordTrace (prefixWord ++ tailWord_3735288) baseStart_3735288 baseEnd_3735288 := by
    simpa [prefixWord, tailWord_3735288, baseEnd_3735288] using wordTrace_append hprefix tailTrace_3735288
  have hstable : (prefixWord ++ tailWord_3735288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3735288).length < 2 ^ (prefixWord ++ tailWord_3735288).sum := by decide
  have hdescent : baseEnd_3735288 < baseStart_3735288 := by decide
  rcases family_descends (prefixWord ++ tailWord_3735288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3735295 : List Nat := [1, 1, 2, 2, 1, 3, 5, 2, 2, 4]
def baseStart_3735295 : Nat := 118140960795 + 3735295 * 2 ^ 59
def prefixEnd_3735295 : Nat := 4983230072969 + 3 ^ 40 * 3735295 * 2
def baseEnd_3735295 : Nat := 639333907112022791611399

theorem tailTrace_3735295 : CollatzResearch.WordTrace tailWord_3735295 prefixEnd_3735295 639333907112022791611399 := by
  unfold tailWord_3735295
  simp only [CollatzResearch.WordTrace]
  refine ⟨136237401002671627442303339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90824934001781084961535559 136237401002671627442303339)
  ·
    refine ⟨204356101504007441163455009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136237401002671627442303339 204356101504007441163455009)
    ·
      refine ⟨153267076128005580872591257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 204356101504007441163455009 153267076128005580872591257)
      ·
        refine ⟨114950307096004185654443443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 153267076128005580872591257 114950307096004185654443443)
        ·
          refine ⟨172425460644006278481665165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114950307096004185654443443 172425460644006278481665165)
          ·
            refine ⟨64659547741502354430624437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 172425460644006278481665165 64659547741502354430624437)
            ·
              refine ⟨6061832600765845727871041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 64659547741502354430624437 6061832600765845727871041)
              ·
                refine ⟨4546374450574384295903281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6061832600765845727871041 4546374450574384295903281)
                ·
                  refine ⟨3409780837930788221927461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4546374450574384295903281 3409780837930788221927461)
                  ·
                    refine ⟨639333907112022791611399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3409780837930788221927461 639333907112022791611399)
                    ·
                      rfl

theorem cell23_3735295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 5, 2, 2, 4].length) (baseStart_3735295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3735295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3735295 prefixEnd_3735295 := by exact prefixLift 3735295
  have htrace : WordTrace (prefixWord ++ tailWord_3735295) baseStart_3735295 baseEnd_3735295 := by
    simpa [prefixWord, tailWord_3735295, baseEnd_3735295] using wordTrace_append hprefix tailTrace_3735295
  have hstable : (prefixWord ++ tailWord_3735295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3735295).length < 2 ^ (prefixWord ++ tailWord_3735295).sum := by decide
  have hdescent : baseEnd_3735295 < baseStart_3735295 := by decide
  rcases family_descends (prefixWord ++ tailWord_3735295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3735301 : List Nat := [1, 3, 1, 1, 2, 1, 1, 1, 1, 4, 7]
def baseStart_3735301 : Nat := 118140960795 + 3735301 * 2 ^ 59
def prefixEnd_3735301 : Nat := 4983230072969 + 3 ^ 40 * 3735301 * 2
def baseEnd_3735301 : Nat := 1918004802219995351359169

theorem tailTrace_3735301 : CollatzResearch.WordTrace tailWord_3735301 prefixEnd_3735301 1918004802219995351359169 := by
  unfold tailWord_3735301
  simp only [CollatzResearch.WordTrace]
  refine ⟨136237619840649890467021757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90825079893766593644681171 136237619840649890467021757)
  ·
    refine ⟨51089107440243708925133159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 136237619840649890467021757 51089107440243708925133159)
    ·
      refine ⟨76633661160365563387699739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51089107440243708925133159 76633661160365563387699739)
      ·
        refine ⟨114950491740548345081549609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76633661160365563387699739 114950491740548345081549609)
        ·
          refine ⟨86212868805411258811162207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114950491740548345081549609 86212868805411258811162207)
          ·
            refine ⟨129319303208116888216743311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86212868805411258811162207 129319303208116888216743311)
            ·
              refine ⟨193978954812175332325114967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 129319303208116888216743311 193978954812175332325114967)
              ·
                refine ⟨290968432218262998487672451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 193978954812175332325114967 290968432218262998487672451)
                ·
                  refine ⟨436452648327394497731508677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 290968432218262998487672451 436452648327394497731508677)
                  ·
                    refine ⟨81834871561386468324657877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 436452648327394497731508677 81834871561386468324657877)
                    ·
                      refine ⟨1918004802219995351359169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 81834871561386468324657877 1918004802219995351359169)
                      ·
                        rfl

theorem cell23_3735301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 1, 1, 4, 7].length) (baseStart_3735301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3735301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3735301 prefixEnd_3735301 := by exact prefixLift 3735301
  have htrace : WordTrace (prefixWord ++ tailWord_3735301) baseStart_3735301 baseEnd_3735301 := by
    simpa [prefixWord, tailWord_3735301, baseEnd_3735301] using wordTrace_append hprefix tailTrace_3735301
  have hstable : (prefixWord ++ tailWord_3735301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3735301).length < 2 ^ (prefixWord ++ tailWord_3735301).sum := by decide
  have hdescent : baseEnd_3735301 < baseStart_3735301 := by decide
  rcases family_descends (prefixWord ++ tailWord_3735301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3735311 : List Nat := [1, 1, 2, 1, 1, 1, 4, 1, 1, 4, 6]
def baseStart_3735311 : Nat := 118140960795 + 3735311 * 2 ^ 59
def prefixEnd_3735311 : Nat := 4983230072969 + 3 ^ 40 * 3735311 * 2
def baseEnd_3735311 : Nat := 1918009937026540312234123

theorem tailTrace_3735311 : CollatzResearch.WordTrace tailWord_3735311 prefixEnd_3735311 1918009937026540312234123 := by
  unfold tailWord_3735311
  simp only [CollatzResearch.WordTrace]
  refine ⟨136237984570613662174885787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90825323047075774783257191 136237984570613662174885787)
  ·
    refine ⟨204356976855920493262328681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136237984570613662174885787 204356976855920493262328681)
    ·
      refine ⟨153267732641940369946746511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 204356976855920493262328681 153267732641940369946746511)
      ·
        refine ⟨229901598962910554920119767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153267732641940369946746511 229901598962910554920119767)
        ·
          refine ⟨344852398444365832380179651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 229901598962910554920119767 344852398444365832380179651)
          ·
            refine ⟨517278597666548748570269477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 344852398444365832380179651 517278597666548748570269477)
            ·
              refine ⟨96989737062477890356925527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 517278597666548748570269477 96989737062477890356925527)
              ·
                refine ⟨145484605593716835535388291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 96989737062477890356925527 145484605593716835535388291)
                ·
                  refine ⟨218226908390575253303082437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 145484605593716835535388291 218226908390575253303082437)
                  ·
                    refine ⟨40917545323232859994327957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 218226908390575253303082437 40917545323232859994327957)
                    ·
                      refine ⟨1918009937026540312234123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 40917545323232859994327957 1918009937026540312234123)
                      ·
                        rfl

theorem cell23_3735311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 1, 1, 4, 6].length) (baseStart_3735311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3735311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3735311 prefixEnd_3735311 := by exact prefixLift 3735311
  have htrace : WordTrace (prefixWord ++ tailWord_3735311) baseStart_3735311 baseEnd_3735311 := by
    simpa [prefixWord, tailWord_3735311, baseEnd_3735311] using wordTrace_append hprefix tailTrace_3735311
  have hstable : (prefixWord ++ tailWord_3735311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3735311).length < 2 ^ (prefixWord ++ tailWord_3735311).sum := by decide
  have hdescent : baseEnd_3735311 < baseStart_3735311 := by decide
  rcases family_descends (prefixWord ++ tailWord_3735311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3735316 : List Nat := [2, 4, 4, 1, 1, 1, 2, 2, 1, 5]
def baseStart_3735316 : Nat := 118140960795 + 3735316 * 2 ^ 59
def prefixEnd_3735316 : Nat := 4983230072969 + 3 ^ 40 * 3735316 * 2
def baseEnd_3735316 : Nat := 639337501476604264223867

theorem tailTrace_3735316 : CollatzResearch.WordTrace tailWord_3735316 prefixEnd_3735316 639337501476604264223867 := by
  unfold tailWord_3735316
  simp only [CollatzResearch.WordTrace]
  refine ⟨68119083467797774014408901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90825444623730365352545201 68119083467797774014408901)
  ·
    refine ⟨12772328150212082627701669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 68119083467797774014408901 12772328150212082627701669)
    ·
      refine ⟨2394811528164765492694063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12772328150212082627701669 2394811528164765492694063)
      ·
        refine ⟨3592217292247148239041095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2394811528164765492694063 3592217292247148239041095)
        ·
          refine ⟨5388325938370722358561643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3592217292247148239041095 5388325938370722358561643)
          ·
            refine ⟨8082488907556083537842465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5388325938370722358561643 8082488907556083537842465)
            ·
              refine ⟨6061866680667062653381849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8082488907556083537842465 6061866680667062653381849)
              ·
                refine ⟨4546400010500296990036387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6061866680667062653381849 4546400010500296990036387)
                ·
                  refine ⟨6819600015750445485054581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4546400010500296990036387 6819600015750445485054581)
                  ·
                    refine ⟨639337501476604264223867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6819600015750445485054581 639337501476604264223867)
                    ·
                      rfl

theorem cell23_3735316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 2, 2, 1, 5].length) (baseStart_3735316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3735316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3735316 prefixEnd_3735316 := by exact prefixLift 3735316
  have htrace : WordTrace (prefixWord ++ tailWord_3735316) baseStart_3735316 baseEnd_3735316 := by
    simpa [prefixWord, tailWord_3735316, baseEnd_3735316] using wordTrace_append hprefix tailTrace_3735316
  have hstable : (prefixWord ++ tailWord_3735316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3735316).length < 2 ^ (prefixWord ++ tailWord_3735316).sum := by decide
  have hdescent : baseEnd_3735316 < baseStart_3735316 := by decide
  rcases family_descends (prefixWord ++ tailWord_3735316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3735321 : List Nat := [1, 2, 1, 2, 1, 1, 1, 2, 3, 9]
def baseStart_3735321 : Nat := 118140960795 + 3735321 * 2 ^ 59
def prefixEnd_3735321 : Nat := 4983230072969 + 3 ^ 40 * 3735321 * 2
def baseEnd_3735321 : Nat := 639338357277695091036359

theorem tailTrace_3735321 : CollatzResearch.WordTrace tailWord_3735321 prefixEnd_3735321 639338357277695091036359 := by
  unfold tailWord_3735321
  simp only [CollatzResearch.WordTrace]
  refine ⟨136238349300577433882749817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90825566200384955921833211 136238349300577433882749817)
  ·
    refine ⟨102178761975433075412062363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136238349300577433882749817 102178761975433075412062363)
    ·
      refine ⟨153268142963149613118093545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102178761975433075412062363 153268142963149613118093545)
      ·
        refine ⟨114951107222362209838570159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 153268142963149613118093545 114951107222362209838570159)
        ·
          refine ⟨172426660833543314757855239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114951107222362209838570159 172426660833543314757855239)
          ·
            refine ⟨258639991250314972136782859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 172426660833543314757855239 258639991250314972136782859)
            ·
              refine ⟨387959986875472458205174289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 258639991250314972136782859 387959986875472458205174289)
              ·
                refine ⟨290969990156604343653880717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 387959986875472458205174289 290969990156604343653880717)
                ·
                  refine ⟨109113746308726628870205269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 290969990156604343653880717 109113746308726628870205269)
                  ·
                    refine ⟨639338357277695091036359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 109113746308726628870205269 639338357277695091036359)
                    ·
                      rfl

theorem cell23_3735321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 2, 3, 9].length) (baseStart_3735321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3735321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3735321 prefixEnd_3735321 := by exact prefixLift 3735321
  have htrace : WordTrace (prefixWord ++ tailWord_3735321) baseStart_3735321 baseEnd_3735321 := by
    simpa [prefixWord, tailWord_3735321, baseEnd_3735321] using wordTrace_append hprefix tailTrace_3735321
  have hstable : (prefixWord ++ tailWord_3735321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3735321).length < 2 ^ (prefixWord ++ tailWord_3735321).sum := by decide
  have hdescent : baseEnd_3735321 < baseStart_3735321 := by decide
  rcases family_descends (prefixWord ++ tailWord_3735321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3735322 : List Nat := [3, 1, 1, 3, 2, 3, 2, 2, 1, 2, 3]
def baseStart_3735322 : Nat := 118140960795 + 3735322 * 2 ^ 59
def prefixEnd_3735322 : Nat := 4983230072969 + 3 ^ 40 * 3735322 * 2
def baseEnd_3735322 : Nat := 1918015585313739769196573

theorem tailTrace_3735322 : CollatzResearch.WordTrace tailWord_3735322 prefixEnd_3735322 1918015585313739769196573 := by
  unfold tailWord_3735322
  simp only [CollatzResearch.WordTrace]
  refine ⟨34059596443393452763384055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90825590515715874035690813 34059596443393452763384055)
  ·
    refine ⟨51089394665090179145076083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34059596443393452763384055 51089394665090179145076083)
    ·
      refine ⟨76634091997635268717614125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51089394665090179145076083 76634091997635268717614125)
      ·
        refine ⟨28737784499113225769105297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76634091997635268717614125 28737784499113225769105297)
        ·
          refine ⟨21553338374334919326828973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28737784499113225769105297 21553338374334919326828973)
          ·
            refine ⟨8082501890375594747560865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21553338374334919326828973 8082501890375594747560865)
            ·
              refine ⟨6061876417781696060670649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8082501890375594747560865 6061876417781696060670649)
              ·
                refine ⟨4546407313336272045502987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6061876417781696060670649 4546407313336272045502987)
                ·
                  refine ⟨6819610970004408068254481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4546407313336272045502987 6819610970004408068254481)
                  ·
                    refine ⟨5114708227503306051190861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6819610970004408068254481 5114708227503306051190861)
                    ·
                      refine ⟨1918015585313739769196573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5114708227503306051190861 1918015585313739769196573)
                      ·
                        rfl

theorem cell23_3735322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 2, 2, 1, 2, 3].length) (baseStart_3735322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3735322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3735322 prefixEnd_3735322 := by exact prefixLift 3735322
  have htrace : WordTrace (prefixWord ++ tailWord_3735322) baseStart_3735322 baseEnd_3735322 := by
    simpa [prefixWord, tailWord_3735322, baseEnd_3735322] using wordTrace_append hprefix tailTrace_3735322
  have hstable : (prefixWord ++ tailWord_3735322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3735322).length < 2 ^ (prefixWord ++ tailWord_3735322).sum := by decide
  have hdescent : baseEnd_3735322 < baseStart_3735322 := by decide
  rcases family_descends (prefixWord ++ tailWord_3735322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3735336 : List Nat := [2, 1, 5, 1, 1, 2, 3, 3, 1, 2, 2]
def baseStart_3735336 : Nat := 118140960795 + 3735336 * 2 ^ 59
def prefixEnd_3735336 : Nat := 4983230072969 + 3 ^ 40 * 3735336 * 2
def baseEnd_3735336 : Nat := 1918022774042902714421509

theorem tailTrace_3735336 : CollatzResearch.WordTrace tailWord_3735336 prefixEnd_3735336 1918022774042902714421509 := by
  unfold tailWord_3735336
  simp only [CollatzResearch.WordTrace]
  refine ⟨68119448197761545722272931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90825930930348727629697241 68119448197761545722272931)
  ·
    refine ⟨102179172296642318583409397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68119448197761545722272931 102179172296642318583409397)
    ·
      refine ⟨9579297402810217367194631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 102179172296642318583409397 9579297402810217367194631)
      ·
        refine ⟨14368946104215326050791947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9579297402810217367194631 14368946104215326050791947)
        ·
          refine ⟨21553419156322989076187921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14368946104215326050791947 21553419156322989076187921)
          ·
            refine ⟨16165064367242241807140941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21553419156322989076187921 16165064367242241807140941)
            ·
              refine ⟨6061899137715840677677853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16165064367242241807140941 6061899137715840677677853)
              ·
                refine ⟨2273212176643440254129195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6061899137715840677677853 2273212176643440254129195)
                ·
                  refine ⟨3409818264965160381193793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2273212176643440254129195 3409818264965160381193793)
                  ·
                    refine ⟨2557363698723870285895345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3409818264965160381193793 2557363698723870285895345)
                    ·
                      refine ⟨1918022774042902714421509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2557363698723870285895345 1918022774042902714421509)
                      ·
                        rfl

theorem cell23_3735336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 3, 3, 1, 2, 2].length) (baseStart_3735336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3735336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3735336 prefixEnd_3735336 := by exact prefixLift 3735336
  have htrace : WordTrace (prefixWord ++ tailWord_3735336) baseStart_3735336 baseEnd_3735336 := by
    simpa [prefixWord, tailWord_3735336, baseEnd_3735336] using wordTrace_append hprefix tailTrace_3735336
  have hstable : (prefixWord ++ tailWord_3735336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3735336).length < 2 ^ (prefixWord ++ tailWord_3735336).sum := by decide
  have hdescent : baseEnd_3735336 < baseStart_3735336 := by decide
  rcases family_descends (prefixWord ++ tailWord_3735336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3735342 : List Nat := [4, 1, 3, 2, 3, 1, 9]
def baseStart_3735342 : Nat := 118140960795 + 3735342 * 2 ^ 59
def prefixEnd_3735342 : Nat := 4983230072969 + 3 ^ 40 * 3735342 * 2
def baseEnd_3735342 : Nat := 23679331542306539394401

theorem tailTrace_3735342 : CollatzResearch.WordTrace tailWord_3735342 prefixEnd_3735342 23679331542306539394401 := by
  unfold tailWord_3735342
  simp only [CollatzResearch.WordTrace]
  refine ⟨17029889404187669308658035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 90826076822334236312842853 17029889404187669308658035)
  ·
    refine ⟨25544834106281503962987053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17029889404187669308658035 25544834106281503962987053)
    ·
      refine ⟨9579312789855563986120145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25544834106281503962987053 9579312789855563986120145)
      ·
        refine ⟨7184484592391672989590109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9579312789855563986120145 7184484592391672989590109)
        ·
          refine ⟨2694181722146877371096291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7184484592391672989590109 2694181722146877371096291)
          ·
            refine ⟨4041272583220316056644437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2694181722146877371096291 4041272583220316056644437)
            ·
              refine ⟨23679331542306539394401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4041272583220316056644437 23679331542306539394401)
              ·
                rfl

theorem cell23_3735342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 3, 1, 9].length) (baseStart_3735342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3735342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3735342 prefixEnd_3735342 := by exact prefixLift 3735342
  have htrace : WordTrace (prefixWord ++ tailWord_3735342) baseStart_3735342 baseEnd_3735342 := by
    simpa [prefixWord, tailWord_3735342, baseEnd_3735342] using wordTrace_append hprefix tailTrace_3735342
  have hstable : (prefixWord ++ tailWord_3735342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3735342).length < 2 ^ (prefixWord ++ tailWord_3735342).sum := by decide
  have hdescent : baseEnd_3735342 < baseStart_3735342 := by decide
  rcases family_descends (prefixWord ++ tailWord_3735342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3735353 : List Nat := [1, 2, 1, 7, 2, 1, 1, 1, 3, 2, 2]
def baseStart_3735353 : Nat := 118140960795 + 3735353 * 2 ^ 59
def prefixEnd_3735353 : Nat := 4983230072969 + 3 ^ 40 * 3735353 * 2
def baseEnd_3735353 : Nat := 1918031503214029147908931

theorem tailTrace_3735353 : CollatzResearch.WordTrace tailWord_3735353 prefixEnd_3735353 1918031503214029147908931 := by
  unfold tailWord_3735353
  simp only [CollatzResearch.WordTrace]
  refine ⟨136239516436461503347914713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90826344290974335565276475 136239516436461503347914713)
  ·
    refine ⟨102179637327346127510936035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136239516436461503347914713 102179637327346127510936035)
    ·
      refine ⟨153269455991019191266404053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102179637327346127510936035 153269455991019191266404053)
      ·
        refine ⟨3592252874789512295306345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 153269455991019191266404053 3592252874789512295306345)
        ·
          refine ⟨2694189656092134221479759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3592252874789512295306345 2694189656092134221479759)
          ·
            refine ⟨4041284484138201332219639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2694189656092134221479759 4041284484138201332219639)
            ·
              refine ⟨6061926726207301998329459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4041284484138201332219639 6061926726207301998329459)
              ·
                refine ⟨9092890089310952997494189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6061926726207301998329459 9092890089310952997494189)
                ·
                  refine ⟨3409833783491607374060321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9092890089310952997494189 3409833783491607374060321)
                  ·
                    refine ⟨2557375337618705530545241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3409833783491607374060321 2557375337618705530545241)
                    ·
                      refine ⟨1918031503214029147908931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2557375337618705530545241 1918031503214029147908931)
                      ·
                        rfl

theorem cell23_3735353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 2, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 2, 1, 1, 1, 3, 2, 2].length) (baseStart_3735353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3735353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3735353 prefixEnd_3735353 := by exact prefixLift 3735353
  have htrace : WordTrace (prefixWord ++ tailWord_3735353) baseStart_3735353 baseEnd_3735353 := by
    simpa [prefixWord, tailWord_3735353, baseEnd_3735353] using wordTrace_append hprefix tailTrace_3735353
  have hstable : (prefixWord ++ tailWord_3735353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3735353).length < 2 ^ (prefixWord ++ tailWord_3735353).sum := by decide
  have hdescent : baseEnd_3735353 < baseStart_3735353 := by decide
  rcases family_descends (prefixWord ++ tailWord_3735353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3735392 : List Nat := [2, 1, 1, 3, 3, 3, 1, 2, 1, 4, 2]
def baseStart_3735392 : Nat := 118140960795 + 3735392 * 2 ^ 59
def prefixEnd_3735392 : Nat := 4983230072969 + 3 ^ 40 * 3735392 * 2
def baseEnd_3735392 : Nat := 1918051528959554495321251

theorem tailTrace_3735392 : CollatzResearch.WordTrace tailWord_3735392 prefixEnd_3735392 1918051528959554495321251 := by
  unfold tailWord_3735392
  simp only [CollatzResearch.WordTrace]
  refine ⟨68120469441660106504292215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90827292588880142005722953 68120469441660106504292215)
  ·
    refine ⟨102180704162490159756438323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68120469441660106504292215 102180704162490159756438323)
    ·
      refine ⟨153271056243735239634657485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102180704162490159756438323 153271056243735239634657485)
      ·
        refine ⟨57476646091400714862996557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 153271056243735239634657485 57476646091400714862996557)
        ·
          refine ⟨21553742284275268073623709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57476646091400714862996557 21553742284275268073623709)
          ·
            refine ⟨8082653356603225527608891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21553742284275268073623709 8082653356603225527608891)
            ·
              refine ⟨12123980034904838291413337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8082653356603225527608891 12123980034904838291413337)
              ·
                refine ⟨9092985026178628718560003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12123980034904838291413337 9092985026178628718560003)
                ·
                  refine ⟨13639477539267943077840005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9092985026178628718560003 13639477539267943077840005)
                  ·
                    refine ⟨2557402038612739327095001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13639477539267943077840005 2557402038612739327095001)
                    ·
                      refine ⟨1918051528959554495321251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2557402038612739327095001 1918051528959554495321251)
                      ·
                        rfl

theorem cell23_3735392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 1, 2, 1, 4, 2].length) (baseStart_3735392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3735392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3735392 prefixEnd_3735392 := by exact prefixLift 3735392
  have htrace : WordTrace (prefixWord ++ tailWord_3735392) baseStart_3735392 baseEnd_3735392 := by
    simpa [prefixWord, tailWord_3735392, baseEnd_3735392] using wordTrace_append hprefix tailTrace_3735392
  have hstable : (prefixWord ++ tailWord_3735392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3735392).length < 2 ^ (prefixWord ++ tailWord_3735392).sum := by decide
  have hdescent : baseEnd_3735392 < baseStart_3735392 := by decide
  rcases family_descends (prefixWord ++ tailWord_3735392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3735396 : List Nat := [2, 3, 1, 1, 5, 1, 3, 1, 1, 3, 2]
def baseStart_3735396 : Nat := 118140960795 + 3735396 * 2 ^ 59
def prefixEnd_3735396 : Nat := 4983230072969 + 3 ^ 40 * 3735396 * 2
def baseEnd_3735396 : Nat := 1918053582882172479671233

theorem tailTrace_3735396 : CollatzResearch.WordTrace tailWord_3735396 prefixEnd_3735396 1918053582882172479671233 := by
  unfold tailWord_3735396
  simp only [CollatzResearch.WordTrace]
  refine ⟨68120542387652860845865021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90827389850203814461153361 68120542387652860845865021)
  ·
    refine ⟨25545203395369822817199383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68120542387652860845865021 25545203395369822817199383)
    ·
      refine ⟨38317805093054734225799075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25545203395369822817199383 38317805093054734225799075)
      ·
        refine ⟨57476707639582101338698613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38317805093054734225799075 57476707639582101338698613)
        ·
          refine ⟨5388441341210822000502995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 57476707639582101338698613 5388441341210822000502995)
          ·
            refine ⟨8082662011816233000754493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5388441341210822000502995 8082662011816233000754493)
            ·
              refine ⟨3030998254431087375282935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8082662011816233000754493 3030998254431087375282935)
              ·
                refine ⟨4546497381646631062924403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3030998254431087375282935 4546497381646631062924403)
                ·
                  refine ⟨6819746072469946594386605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4546497381646631062924403 6819746072469946594386605)
                  ·
                    refine ⟨2557404777176229972894977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6819746072469946594386605 2557404777176229972894977)
                    ·
                      refine ⟨1918053582882172479671233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2557404777176229972894977 1918053582882172479671233)
                      ·
                        rfl

theorem cell23_3735396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 3, 1, 1, 3, 2].length) (baseStart_3735396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3735396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3735396 prefixEnd_3735396 := by exact prefixLift 3735396
  have htrace : WordTrace (prefixWord ++ tailWord_3735396) baseStart_3735396 baseEnd_3735396 := by
    simpa [prefixWord, tailWord_3735396, baseEnd_3735396] using wordTrace_append hprefix tailTrace_3735396
  have hstable : (prefixWord ++ tailWord_3735396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3735396).length < 2 ^ (prefixWord ++ tailWord_3735396).sum := by decide
  have hdescent : baseEnd_3735396 < baseStart_3735396 := by decide
  rcases family_descends (prefixWord ++ tailWord_3735396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3735409 : List Nat := [1, 2, 2, 2, 1, 3, 4, 2, 2, 2, 2]
def baseStart_3735409 : Nat := 118140960795 + 3735409 * 2 ^ 59
def prefixEnd_3735409 : Nat := 4983230072969 + 3 ^ 40 * 3735409 * 2
def baseEnd_3735409 : Nat := 1918060258130680928808673

theorem tailTrace_3735409 : CollatzResearch.WordTrace tailWord_3735409 prefixEnd_3735409 1918060258130680928808673 := by
  unfold tailWord_3735409
  simp only [CollatzResearch.WordTrace]
  refine ⟨136241558924258624911953281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90827705949505749941302187 136241558924258624911953281)
  ·
    refine ⟨102181169193193968683964961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136241558924258624911953281 102181169193193968683964961)
    ·
      refine ⟨76635876894895476512973721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102181169193193968683964961 76635876894895476512973721)
      ·
        refine ⟨57476907671171607384730291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76635876894895476512973721 57476907671171607384730291)
        ·
          refine ⟨86215361506757411077095437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57476907671171607384730291 86215361506757411077095437)
          ·
            refine ⟨32330760565034029153910789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 86215361506757411077095437 32330760565034029153910789)
            ·
              refine ⟨6062017605943880466358273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32330760565034029153910789 6062017605943880466358273)
              ·
                refine ⟨4546513204457910349768705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6062017605943880466358273 4546513204457910349768705)
                ·
                  refine ⟨3409884903343432762326529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4546513204457910349768705 3409884903343432762326529)
                  ·
                    refine ⟨2557413677507574571744897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3409884903343432762326529 2557413677507574571744897)
                    ·
                      refine ⟨1918060258130680928808673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2557413677507574571744897 1918060258130680928808673)
                      ·
                        rfl

theorem cell23_3735409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 4, 2, 2, 2, 2].length) (baseStart_3735409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3735409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3735409 prefixEnd_3735409 := by exact prefixLift 3735409
  have htrace : WordTrace (prefixWord ++ tailWord_3735409) baseStart_3735409 baseEnd_3735409 := by
    simpa [prefixWord, tailWord_3735409, baseEnd_3735409] using wordTrace_append hprefix tailTrace_3735409
  have hstable : (prefixWord ++ tailWord_3735409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3735409).length < 2 ^ (prefixWord ++ tailWord_3735409).sum := by decide
  have hdescent : baseEnd_3735409 < baseStart_3735409 := by decide
  rcases family_descends (prefixWord ++ tailWord_3735409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3735422 : List Nat := [4, 2, 3, 1, 1, 1, 1, 1, 1, 4, 4]
def baseStart_3735422 : Nat := 118140960795 + 3735422 * 2 ^ 59
def prefixEnd_3735422 : Nat := 4983230072969 + 3 ^ 40 * 3735422 * 2
def baseEnd_3735422 : Nat := 1918066933379189377946113

theorem tailTrace_3735422 : CollatzResearch.WordTrace tailWord_3735422 prefixEnd_3735422 1918066933379189377946113 := by
  unfold tailWord_3735422
  simp only [CollatzResearch.WordTrace]
  refine ⟨17030254134151441016522065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 90828022048807685421451013 17030254134151441016522065)
  ·
    refine ⟨12772690600613580762391549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17030254134151441016522065 12772690600613580762391549)
    ·
      refine ⟨4789758975230092785896831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12772690600613580762391549 4789758975230092785896831)
      ·
        refine ⟨7184638462845139178845247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4789758975230092785896831 7184638462845139178845247)
        ·
          refine ⟨10776957694267708768267871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7184638462845139178845247 10776957694267708768267871)
          ·
            refine ⟨16165436541401563152401807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10776957694267708768267871 16165436541401563152401807)
            ·
              refine ⟨24248154812102344728602711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16165436541401563152401807 24248154812102344728602711)
              ·
                refine ⟨36372232218153517092904067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24248154812102344728602711 36372232218153517092904067)
                ·
                  refine ⟨54558348327230275639356101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36372232218153517092904067 54558348327230275639356101)
                  ·
                    refine ⟨10229690311355676682379269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 54558348327230275639356101 10229690311355676682379269)
                    ·
                      refine ⟨1918066933379189377946113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10229690311355676682379269 1918066933379189377946113)
                      ·
                        rfl

theorem cell23_3735422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 1, 1, 1, 4, 4].length) (baseStart_3735422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3735422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3735422 prefixEnd_3735422 := by exact prefixLift 3735422
  have htrace : WordTrace (prefixWord ++ tailWord_3735422) baseStart_3735422 baseEnd_3735422 := by
    simpa [prefixWord, tailWord_3735422, baseEnd_3735422] using wordTrace_append hprefix tailTrace_3735422
  have hstable : (prefixWord ++ tailWord_3735422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3735422).length < 2 ^ (prefixWord ++ tailWord_3735422).sum := by decide
  have hdescent : baseEnd_3735422 < baseStart_3735422 := by decide
  rcases family_descends (prefixWord ++ tailWord_3735422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3735435 : List Nat := [1, 1, 1, 1, 4, 2, 1, 1, 4, 5, 2]
def baseStart_3735435 : Nat := 118140960795 + 3735435 * 2 ^ 59
def prefixEnd_3735435 : Nat := 4983230072969 + 3 ^ 40 * 3735435 * 2
def baseEnd_3735435 : Nat := 1918073608627697827083553

theorem tailTrace_3735435 : CollatzResearch.WordTrace tailWord_3735435 prefixEnd_3735435 1918073608627697827083553 := by
  unfold tailWord_3735435
  simp only [CollatzResearch.WordTrace]
  refine ⟨136242507222164431352399759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90828338148109620901599839 136242507222164431352399759)
  ·
    refine ⟨204363760833246647028599639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136242507222164431352399759 204363760833246647028599639)
    ·
      refine ⟨306545641249869970542899459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204363760833246647028599639 306545641249869970542899459)
      ·
        refine ⟨459818461874804955814349189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 306545641249869970542899459 459818461874804955814349189)
        ·
          refine ⟨86215961601525929215190473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 459818461874804955814349189 86215961601525929215190473)
          ·
            refine ⟨64661971201144446911392855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86215961601525929215190473 64661971201144446911392855)
            ·
              refine ⟨96992956801716670367089283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64661971201144446911392855 96992956801716670367089283)
              ·
                refine ⟨145489435202575005550633925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 96992956801716670367089283 145489435202575005550633925)
                ·
                  refine ⟨27279269100482813540743861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 145489435202575005550633925 27279269100482813540743861)
                  ·
                    refine ⟨2557431478170263769444737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 27279269100482813540743861 2557431478170263769444737)
                    ·
                      refine ⟨1918073608627697827083553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2557431478170263769444737 1918073608627697827083553)
                      ·
                        rfl

theorem cell23_3735435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 1, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 1, 4, 5, 2].length) (baseStart_3735435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3735435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3735435 prefixEnd_3735435 := by exact prefixLift 3735435
  have htrace : WordTrace (prefixWord ++ tailWord_3735435) baseStart_3735435 baseEnd_3735435 := by
    simpa [prefixWord, tailWord_3735435, baseEnd_3735435] using wordTrace_append hprefix tailTrace_3735435
  have hstable : (prefixWord ++ tailWord_3735435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3735435).length < 2 ^ (prefixWord ++ tailWord_3735435).sum := by decide
  have hdescent : baseEnd_3735435 < baseStart_3735435 := by decide
  rcases family_descends (prefixWord ++ tailWord_3735435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3735502 : List Nat := [4, 1, 1, 1, 2, 2, 2, 3, 2, 2, 3]
def baseStart_3735502 : Nat := 118140960795 + 3735502 * 2 ^ 59
def prefixEnd_3735502 : Nat := 4983230072969 + 3 ^ 40 * 3735502 * 2
def baseEnd_3735502 : Nat := 1918108011831549064945745

theorem tailTrace_3735502 : CollatzResearch.WordTrace tailWord_3735502 prefixEnd_3735502 1918108011831549064945745 := by
  unfold tailWord_3735502
  simp only [CollatzResearch.WordTrace]
  refine ⟨17030618864115212724386095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 90829967275281134530059173 17030618864115212724386095)
  ·
    refine ⟨25545928296172819086579143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17030618864115212724386095 25545928296172819086579143)
    ·
      refine ⟨38318892444259228629868715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25545928296172819086579143 38318892444259228629868715)
      ·
        refine ⟨57478338666388842944803073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38318892444259228629868715 57478338666388842944803073)
        ·
          refine ⟨43108753999791632208602305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57478338666388842944803073 43108753999791632208602305)
          ·
            refine ⟨32331565499843724156451729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43108753999791632208602305 32331565499843724156451729)
            ·
              refine ⟨24248674124882793117338797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32331565499843724156451729 24248674124882793117338797)
              ·
                refine ⟨9093252796831047419002049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24248674124882793117338797 9093252796831047419002049)
                ·
                  refine ⟨6819939597623285564251537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9093252796831047419002049 6819939597623285564251537)
                  ·
                    refine ⟨5114954698217464173188653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6819939597623285564251537 5114954698217464173188653)
                    ·
                      refine ⟨1918108011831549064945745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5114954698217464173188653 1918108011831549064945745)
                      ·
                        rfl

theorem cell23_3735502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 2, 3, 2, 2, 3].length) (baseStart_3735502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3735502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3735502 prefixEnd_3735502 := by exact prefixLift 3735502
  have htrace : WordTrace (prefixWord ++ tailWord_3735502) baseStart_3735502 baseEnd_3735502 := by
    simpa [prefixWord, tailWord_3735502, baseEnd_3735502] using wordTrace_append hprefix tailTrace_3735502
  have hstable : (prefixWord ++ tailWord_3735502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3735502).length < 2 ^ (prefixWord ++ tailWord_3735502).sum := by decide
  have hdescent : baseEnd_3735502 < baseStart_3735502 := by decide
  rcases family_descends (prefixWord ++ tailWord_3735502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3735535 : List Nat := [1, 1, 2, 1, 4, 2, 2, 2, 3, 5]
def baseStart_3735535 : Nat := 118140960795 + 3735535 * 2 ^ 59
def prefixEnd_3735535 : Nat := 4983230072969 + 3 ^ 40 * 3735535 * 2
def baseEnd_3735535 : Nat := 639374985564382478611031

theorem tailTrace_3735535 : CollatzResearch.WordTrace tailWord_3735535 prefixEnd_3735535 639374985564382478611031 := by
  unfold tailWord_3735535
  simp only [CollatzResearch.WordTrace]
  refine ⟨136246154521802148431040059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90830769681201432287360039 136246154521802148431040059)
  ·
    refine ⟨204369231782703222646560089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136246154521802148431040059 204369231782703222646560089)
    ·
      refine ⟨153276923837027416984920067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 204369231782703222646560089 153276923837027416984920067)
      ·
        refine ⟨229915385755541125477380101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153276923837027416984920067 229915385755541125477380101)
        ·
          refine ⟨43109134829163961027008769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 229915385755541125477380101 43109134829163961027008769)
          ·
            refine ⟨32331851121872970770256577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43109134829163961027008769 32331851121872970770256577)
            ·
              refine ⟨24248888341404728077692433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32331851121872970770256577 24248888341404728077692433)
              ·
                refine ⟨18186666256053546058269325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24248888341404728077692433 18186666256053546058269325)
                ·
                  refine ⟨6819999846020079771850997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18186666256053546058269325 6819999846020079771850997)
                  ·
                    refine ⟨639374985564382478611031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6819999846020079771850997 639374985564382478611031)
                    ·
                      rfl

theorem cell23_3735535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 2, 2, 3, 5].length) (baseStart_3735535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3735535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3735535 prefixEnd_3735535 := by exact prefixLift 3735535
  have htrace : WordTrace (prefixWord ++ tailWord_3735535) baseStart_3735535 baseEnd_3735535 := by
    simpa [prefixWord, tailWord_3735535, baseEnd_3735535] using wordTrace_append hprefix tailTrace_3735535
  have hstable : (prefixWord ++ tailWord_3735535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3735535).length < 2 ^ (prefixWord ++ tailWord_3735535).sum := by decide
  have hdescent : baseEnd_3735535 < baseStart_3735535 := by decide
  rcases family_descends (prefixWord ++ tailWord_3735535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3735559 : List Nat := [1, 1, 4, 3, 1, 2, 1, 3, 2, 3, 2]
def baseStart_3735559 : Nat := 118140960795 + 3735559 * 2 ^ 59
def prefixEnd_3735559 : Nat := 4983230072969 + 3 ^ 40 * 3735559 * 2
def baseEnd_3735559 : Nat := 1918137280228855341932983

theorem tailTrace_3735559 : CollatzResearch.WordTrace tailWord_3735559 prefixEnd_3735559 1918137280228855341932983 := by
  unfold tailWord_3735559
  simp only [CollatzResearch.WordTrace]
  refine ⟨136247029873715200529913731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90831353249143467019942487 136247029873715200529913731)
  ·
    refine ⟨204370544810572800794870597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136247029873715200529913731 204370544810572800794870597)
    ·
      refine ⟨38319477151982400149038237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 204370544810572800794870597 38319477151982400149038237)
      ·
        refine ⟨14369803931993400055889339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38319477151982400149038237 14369803931993400055889339)
        ·
          refine ⟨21554705897990100083834009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14369803931993400055889339 21554705897990100083834009)
          ·
            refine ⟨16166029423492575062875507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21554705897990100083834009 16166029423492575062875507)
            ·
              refine ⟨24249044135238862594313261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16166029423492575062875507 24249044135238862594313261)
              ·
                refine ⟨9093391550714573472867473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24249044135238862594313261 9093391550714573472867473)
                ·
                  refine ⟨6820043663035930104650605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9093391550714573472867473 6820043663035930104650605)
                  ·
                    refine ⟨2557516373638473789243977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6820043663035930104650605 2557516373638473789243977)
                    ·
                      refine ⟨1918137280228855341932983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2557516373638473789243977 1918137280228855341932983)
                      ·
                        rfl

theorem cell23_3735559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 1, 3, 2, 3, 2].length) (baseStart_3735559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3735559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3735559 prefixEnd_3735559 := by exact prefixLift 3735559
  have htrace : WordTrace (prefixWord ++ tailWord_3735559) baseStart_3735559 baseEnd_3735559 := by
    simpa [prefixWord, tailWord_3735559, baseEnd_3735559] using wordTrace_append hprefix tailTrace_3735559
  have hstable : (prefixWord ++ tailWord_3735559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3735559).length < 2 ^ (prefixWord ++ tailWord_3735559).sum := by decide
  have hdescent : baseEnd_3735559 < baseStart_3735559 := by decide
  rcases family_descends (prefixWord ++ tailWord_3735559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3735566 : List Nat := [4, 1, 1, 2, 2, 1, 2, 5, 1, 1, 3]
def baseStart_3735566 : Nat := 118140960795 + 3735566 * 2 ^ 59
def prefixEnd_3735566 : Nat := 4983230072969 + 3 ^ 40 * 3735566 * 2
def baseEnd_3735566 : Nat := 1918140874593436814545451

theorem tailTrace_3735566 : CollatzResearch.WordTrace tailWord_3735566 prefixEnd_3735566 1918140874593436814545451 := by
  unfold tailWord_3735566
  simp only [CollatzResearch.WordTrace]
  refine ⟨17030910648086230090677319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 90831523456459893816945701 17030910648086230090677319)
  ·
    refine ⟨25546365972129345136015979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17030910648086230090677319 25546365972129345136015979)
    ·
      refine ⟨38319548958194017704023969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25546365972129345136015979 38319548958194017704023969)
      ·
        refine ⟨28739661718645513278017977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38319548958194017704023969 28739661718645513278017977)
        ·
          refine ⟨21554746288984134958513483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28739661718645513278017977 21554746288984134958513483)
          ·
            refine ⟨32332119433476202437770225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21554746288984134958513483 32332119433476202437770225)
            ·
              refine ⟨24249089575107151828327669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32332119433476202437770225 24249089575107151828327669)
              ·
                refine ⟨2273352147666295483905719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24249089575107151828327669 2273352147666295483905719)
                ·
                  refine ⟨3410028221499443225858579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2273352147666295483905719 3410028221499443225858579)
                  ·
                    refine ⟨5115042332249164838787869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3410028221499443225858579 5115042332249164838787869)
                    ·
                      refine ⟨1918140874593436814545451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5115042332249164838787869 1918140874593436814545451)
                      ·
                        rfl

theorem cell23_3735566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 2, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 2, 5, 1, 1, 3].length) (baseStart_3735566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3735566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3735566 prefixEnd_3735566 := by exact prefixLift 3735566
  have htrace : WordTrace (prefixWord ++ tailWord_3735566) baseStart_3735566 baseEnd_3735566 := by
    simpa [prefixWord, tailWord_3735566, baseEnd_3735566] using wordTrace_append hprefix tailTrace_3735566
  have hstable : (prefixWord ++ tailWord_3735566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3735566).length < 2 ^ (prefixWord ++ tailWord_3735566).sum := by decide
  have hdescent : baseEnd_3735566 < baseStart_3735566 := by decide
  rcases family_descends (prefixWord ++ tailWord_3735566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3735602 : List Nat := [3, 2, 1, 1, 2, 3, 1, 3, 1, 2, 4]
def baseStart_3735602 : Nat := 118140960795 + 3735602 * 2 ^ 59
def prefixEnd_3735602 : Nat := 4983230072969 + 3 ^ 40 * 3735602 * 2
def baseEnd_3735602 : Nat := 1918159359896998673695285

theorem tailTrace_3735602 : CollatzResearch.WordTrace tailWord_3735602 prefixEnd_3735602 1918159359896998673695285 := by
  unfold tailWord_3735602
  simp only [CollatzResearch.WordTrace]
  refine ⟨34062149553139854718432265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90832398808372945915819373 34062149553139854718432265)
  ·
    refine ⟨25546612164854891038824199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34062149553139854718432265 25546612164854891038824199)
    ·
      refine ⟨38319918247282336558236299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25546612164854891038824199 38319918247282336558236299)
      ·
        refine ⟨57479877370923504837354449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38319918247282336558236299 57479877370923504837354449)
        ·
          refine ⟨43109908028192628628015837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57479877370923504837354449 43109908028192628628015837)
          ·
            refine ⟨16166215510572235735505939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43109908028192628628015837 16166215510572235735505939)
            ·
              refine ⟨24249323265858353603258909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16166215510572235735505939 24249323265858353603258909)
              ·
                refine ⟨9093496224696882601222091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24249323265858353603258909 9093496224696882601222091)
                ·
                  refine ⟨13640244337045323901833137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9093496224696882601222091 13640244337045323901833137)
                  ·
                    refine ⟨10230183252783992926374853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13640244337045323901833137 10230183252783992926374853)
                    ·
                      refine ⟨1918159359896998673695285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10230183252783992926374853 1918159359896998673695285)
                      ·
                        rfl

theorem cell23_3735602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 1, 3, 1, 2, 4].length) (baseStart_3735602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3735602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3735602 prefixEnd_3735602 := by exact prefixLift 3735602
  have htrace : WordTrace (prefixWord ++ tailWord_3735602) baseStart_3735602 baseEnd_3735602 := by
    simpa [prefixWord, tailWord_3735602, baseEnd_3735602] using wordTrace_append hprefix tailTrace_3735602
  have hstable : (prefixWord ++ tailWord_3735602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3735602).length < 2 ^ (prefixWord ++ tailWord_3735602).sum := by decide
  have hdescent : baseEnd_3735602 < baseStart_3735602 := by decide
  rcases family_descends (prefixWord ++ tailWord_3735602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3735612 : List Nat := [2, 2, 2, 2, 2, 1, 5, 7]
def baseStart_3735612 : Nat := 118140960795 + 3735612 * 2 ^ 59
def prefixEnd_3735612 : Nat := 4983230072969 + 3 ^ 40 * 3735612 * 2
def baseEnd_3735612 : Nat := 71043129433464579058157

theorem tailTrace_3735612 : CollatzResearch.WordTrace tailWord_3735612 prefixEnd_3735612 71043129433464579058157 := by
  unfold tailWord_3735612
  simp only [CollatzResearch.WordTrace]
  refine ⟨68124481471261595290796545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90832641961682127054395393 68124481471261595290796545)
  ·
    refine ⟨51093361103446196468097409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68124481471261595290796545 51093361103446196468097409)
    ·
      refine ⟨38320020827584647351073057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51093361103446196468097409 38320020827584647351073057)
      ·
        refine ⟨28740015620688485513304793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38320020827584647351073057 28740015620688485513304793)
        ·
          refine ⟨21555011715516364134978595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28740015620688485513304793 21555011715516364134978595)
          ·
            refine ⟨32332517573274546202467893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21555011715516364134978595 32332517573274546202467893)
            ·
              refine ⟨3031173522494488706481365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 32332517573274546202467893 3031173522494488706481365)
              ·
                refine ⟨71043129433464579058157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3031173522494488706481365 71043129433464579058157)
                ·
                  rfl

theorem cell23_3735612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 5, 7].length) (baseStart_3735612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3735612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3735612 prefixEnd_3735612 := by exact prefixLift 3735612
  have htrace : WordTrace (prefixWord ++ tailWord_3735612) baseStart_3735612 baseEnd_3735612 := by
    simpa [prefixWord, tailWord_3735612, baseEnd_3735612] using wordTrace_append hprefix tailTrace_3735612
  have hstable : (prefixWord ++ tailWord_3735612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3735612).length < 2 ^ (prefixWord ++ tailWord_3735612).sum := by decide
  have hdescent : baseEnd_3735612 < baseStart_3735612 := by decide
  rcases family_descends (prefixWord ++ tailWord_3735612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3735623 : List Nat := [1, 1, 4, 1, 3, 1, 4, 3, 1, 2, 2]
def baseStart_3735623 : Nat := 118140960795 + 3735623 * 2 ^ 59
def prefixEnd_3735623 : Nat := 4983230072969 + 3 ^ 40 * 3735623 * 2
def baseEnd_3735623 : Nat := 1918170142990743091532689

theorem tailTrace_3735623 : CollatzResearch.WordTrace tailWord_3735623 prefixEnd_3735623 1918170142990743091532689 := by
  unfold tailWord_3735623
  simp only [CollatzResearch.WordTrace]
  refine ⟨136249364145483339460243523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90832909430322226306829015 136249364145483339460243523)
  ·
    refine ⟨204374046218225009190365285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136249364145483339460243523 204374046218225009190365285)
    ·
      refine ⟨38320133665917189223193491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 204374046218225009190365285 38320133665917189223193491)
      ·
        refine ⟨57480200498875783834790237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38320133665917189223193491 57480200498875783834790237)
        ·
          refine ⟨21555075187078418938046339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57480200498875783834790237 21555075187078418938046339)
          ·
            refine ⟨32332612780617628407069509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21555075187078418938046339 32332612780617628407069509)
            ·
              refine ⟨6062364896365805326325533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32332612780617628407069509 6062364896365805326325533)
              ·
                refine ⟨2273386836137176997372075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6062364896365805326325533 2273386836137176997372075)
                ·
                  refine ⟨3410080254205765496058113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2273386836137176997372075 3410080254205765496058113)
                  ·
                    refine ⟨2557560190654324122043585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3410080254205765496058113 2557560190654324122043585)
                    ·
                      refine ⟨1918170142990743091532689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2557560190654324122043585 1918170142990743091532689)
                      ·
                        rfl

theorem cell23_3735623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 4, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 4, 3, 1, 2, 2].length) (baseStart_3735623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3735623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3735623 prefixEnd_3735623 := by exact prefixLift 3735623
  have htrace : WordTrace (prefixWord ++ tailWord_3735623) baseStart_3735623 baseEnd_3735623 := by
    simpa [prefixWord, tailWord_3735623, baseEnd_3735623] using wordTrace_append hprefix tailTrace_3735623
  have hstable : (prefixWord ++ tailWord_3735623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3735623).length < 2 ^ (prefixWord ++ tailWord_3735623).sum := by decide
  have hdescent : baseEnd_3735623 < baseStart_3735623 := by decide
  rcases family_descends (prefixWord ++ tailWord_3735623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3735666 : List Nat := [3, 2, 1, 2, 2, 2, 1, 4, 1, 3, 2]
def baseStart_3735666 : Nat := 118140960795 + 3735666 * 2 ^ 59
def prefixEnd_3735666 : Nat := 4983230072969 + 3 ^ 40 * 3735666 * 2
def baseEnd_3735666 : Nat := 1918192222658886423294991

theorem tailTrace_3735666 : CollatzResearch.WordTrace tailWord_3735666 prefixEnd_3735666 1918192222658886423294991 := by
  unfold tailWord_3735666
  simp only [CollatzResearch.WordTrace]
  refine ⟨34062733121081889451014713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90833954989551705202705901 34062733121081889451014713)
  ·
    refine ⟨25547049840811417088261035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34062733121081889451014713 25547049840811417088261035)
    ·
      refine ⟨38320574761217125632391553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25547049840811417088261035 38320574761217125632391553)
      ·
        refine ⟨28740431070912844224293665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38320574761217125632391553 28740431070912844224293665)
        ·
          refine ⟨21555323303184633168220249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28740431070912844224293665 21555323303184633168220249)
          ·
            refine ⟨16166492477388474876165187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21555323303184633168220249 16166492477388474876165187)
            ·
              refine ⟨24249738716082712314247781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16166492477388474876165187 24249738716082712314247781)
              ·
                refine ⟨4546826009265508558921459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24249738716082712314247781 4546826009265508558921459)
                ·
                  refine ⟨6820239013898262838382189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4546826009265508558921459 6820239013898262838382189)
                  ·
                    refine ⟨2557589630211848564393321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6820239013898262838382189 2557589630211848564393321)
                    ·
                      refine ⟨1918192222658886423294991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2557589630211848564393321 1918192222658886423294991)
                      ·
                        rfl

theorem cell23_3735666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 1, 4, 1, 3, 2].length) (baseStart_3735666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3735666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3735666 prefixEnd_3735666 := by exact prefixLift 3735666
  have htrace : WordTrace (prefixWord ++ tailWord_3735666) baseStart_3735666 baseEnd_3735666 := by
    simpa [prefixWord, tailWord_3735666, baseEnd_3735666] using wordTrace_append hprefix tailTrace_3735666
  have hstable : (prefixWord ++ tailWord_3735666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3735666).length < 2 ^ (prefixWord ++ tailWord_3735666).sum := by decide
  have hdescent : baseEnd_3735666 < baseStart_3735666 := by decide
  rcases family_descends (prefixWord ++ tailWord_3735666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3735696 : List Nat := [2, 1, 1, 1, 1, 1, 6, 4, 2, 2, 2]
def baseStart_3735696 : Nat := 118140960795 + 3735696 * 2 ^ 59
def prefixEnd_3735696 : Nat := 4983230072969 + 3 ^ 40 * 3735696 * 2
def baseEnd_3735696 : Nat := 1918207627078521305919853

theorem tailTrace_3735696 : CollatzResearch.WordTrace tailWord_3735696 prefixEnd_3735696 1918207627078521305919853 := by
  unfold tailWord_3735696
  simp only [CollatzResearch.WordTrace]
  refine ⟨68126013337109436463825471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90834684449479248618433961 68126013337109436463825471)
  ·
    refine ⟨102189020005664154695738207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68126013337109436463825471 102189020005664154695738207)
    ·
      refine ⟨153283530008496232043607311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102189020005664154695738207 153283530008496232043607311)
      ·
        refine ⟨229925295012744348065410967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153283530008496232043607311 229925295012744348065410967)
        ·
          refine ⟨344887942519116522098116451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 229925295012744348065410967 344887942519116522098116451)
          ·
            refine ⟨517331913778674783147174677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 344887942519116522098116451 517331913778674783147174677)
            ·
              refine ⟨24249933458375380460023813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 517331913778674783147174677 24249933458375380460023813)
              ·
                refine ⟨4546862523445383836254465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24249933458375380460023813 4546862523445383836254465)
                ·
                  refine ⟨3410146892584037877190849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4546862523445383836254465 3410146892584037877190849)
                  ·
                    refine ⟨2557610169438028407893137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3410146892584037877190849 2557610169438028407893137)
                    ·
                      refine ⟨1918207627078521305919853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2557610169438028407893137 1918207627078521305919853)
                      ·
                        rfl

theorem cell23_3735696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 6, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 6, 4, 2, 2, 2].length) (baseStart_3735696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3735696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3735696 prefixEnd_3735696 := by exact prefixLift 3735696
  have htrace : WordTrace (prefixWord ++ tailWord_3735696) baseStart_3735696 baseEnd_3735696 := by
    simpa [prefixWord, tailWord_3735696, baseEnd_3735696] using wordTrace_append hprefix tailTrace_3735696
  have hstable : (prefixWord ++ tailWord_3735696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3735696).length < 2 ^ (prefixWord ++ tailWord_3735696).sum := by decide
  have hdescent : baseEnd_3735696 < baseStart_3735696 := by decide
  rcases family_descends (prefixWord ++ tailWord_3735696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3735713 : List Nat := [1, 2, 3, 3, 1, 3, 1, 3, 2, 2, 2]
def baseStart_3735713 : Nat := 118140960795 + 3735713 * 2 ^ 59
def prefixEnd_3735713 : Nat := 4983230072969 + 3 ^ 40 * 3735713 * 2
def baseEnd_3735713 : Nat := 1918216356249647739407275

theorem tailTrace_3735713 : CollatzResearch.WordTrace tailWord_3735713 prefixEnd_3735713 1918216356249647739407275 := by
  unfold tailWord_3735713
  simp only [CollatzResearch.WordTrace]
  refine ⟨136252646715157284831019793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90835097810104856554013195 136252646715157284831019793)
  ·
    refine ⟨102189485036367963623264845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136252646715157284831019793 102189485036367963623264845)
    ·
      refine ⟨38321056888637986358724317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102189485036367963623264845 38321056888637986358724317)
      ·
        refine ⟨14370396333239244884521619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38321056888637986358724317 14370396333239244884521619)
        ·
          refine ⟨21555594499858867326782429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14370396333239244884521619 21555594499858867326782429)
          ·
            refine ⟨8083347937447075247543411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21555594499858867326782429 8083347937447075247543411)
            ·
              refine ⟨12125021906170612871315117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8083347937447075247543411 12125021906170612871315117)
              ·
                refine ⟨4546883214813979826743169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12125021906170612871315117 4546883214813979826743169)
                ·
                  refine ⟨3410162411110484870057377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4546883214813979826743169 3410162411110484870057377)
                  ·
                    refine ⟨2557621808332863652543033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3410162411110484870057377 2557621808332863652543033)
                    ·
                      refine ⟨1918216356249647739407275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2557621808332863652543033 1918216356249647739407275)
                      ·
                        rfl

theorem cell23_3735713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 1, 3, 2, 2, 2].length) (baseStart_3735713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3735713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3735713 prefixEnd_3735713 := by exact prefixLift 3735713
  have htrace : WordTrace (prefixWord ++ tailWord_3735713) baseStart_3735713 baseEnd_3735713 := by
    simpa [prefixWord, tailWord_3735713, baseEnd_3735713] using wordTrace_append hprefix tailTrace_3735713
  have hstable : (prefixWord ++ tailWord_3735713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3735713).length < 2 ^ (prefixWord ++ tailWord_3735713).sum := by decide
  have hdescent : baseEnd_3735713 < baseStart_3735713 := by decide
  rcases family_descends (prefixWord ++ tailWord_3735713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3735752 : List Nat := [2, 1, 3, 1, 2, 1, 1, 2, 3, 3, 4]
def baseStart_3735752 : Nat := 118140960795 + 3735752 * 2 ^ 59
def prefixEnd_3735752 : Nat := 4983230072969 + 3 ^ 40 * 3735752 * 2
def baseEnd_3735752 : Nat := 1918236381995173086819595

theorem tailTrace_3735752 : CollatzResearch.WordTrace tailWord_3735752 prefixEnd_3735752 1918236381995173086819595 := by
  unfold tailWord_3735752
  simp only [CollatzResearch.WordTrace]
  refine ⟨68127034581007997245844755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90836046108010662994459673 68127034581007997245844755)
  ·
    refine ⟨102190551871511995868767133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68127034581007997245844755 102190551871511995868767133)
    ·
      refine ⟨38321456951816998450787675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102190551871511995868767133 38321456951816998450787675)
      ·
        refine ⟨57482185427725497676181513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38321456951816998450787675 57482185427725497676181513)
        ·
          refine ⟨43111639070794123257136135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57482185427725497676181513 43111639070794123257136135)
          ·
            refine ⟨64667458606191184885704203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43111639070794123257136135 64667458606191184885704203)
            ·
              refine ⟨97001187909286777328556305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64667458606191184885704203 97001187909286777328556305)
              ·
                refine ⟨72750890931965082996417229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 97001187909286777328556305 72750890931965082996417229)
                ·
                  refine ⟨27281584099486906123656461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 72750890931965082996417229 27281584099486906123656461)
                  ·
                    refine ⟨10230594037307589796371173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27281584099486906123656461 10230594037307589796371173)
                    ·
                      refine ⟨1918236381995173086819595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10230594037307589796371173 1918236381995173086819595)
                      ·
                        rfl

theorem cell23_3735752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 2, 3, 3, 4].length) (baseStart_3735752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3735752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3735752 prefixEnd_3735752 := by exact prefixLift 3735752
  have htrace : WordTrace (prefixWord ++ tailWord_3735752) baseStart_3735752 baseEnd_3735752 := by
    simpa [prefixWord, tailWord_3735752, baseEnd_3735752] using wordTrace_append hprefix tailTrace_3735752
  have hstable : (prefixWord ++ tailWord_3735752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3735752).length < 2 ^ (prefixWord ++ tailWord_3735752).sum := by decide
  have hdescent : baseEnd_3735752 < baseStart_3735752 := by decide
  rcases family_descends (prefixWord ++ tailWord_3735752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3735769 : List Nat := [1, 2, 1, 2, 3, 1, 3, 1, 1, 6, 2]
def baseStart_3735769 : Nat := 118140960795 + 3735769 * 2 ^ 59
def prefixEnd_3735769 : Nat := 4983230072969 + 3 ^ 40 * 3735769 * 2
def baseEnd_3735769 : Nat := 1918245111166299520307017

theorem tailTrace_3735769 : CollatzResearch.WordTrace tailWord_3735769 prefixEnd_3735769 1918245111166299520307017 := by
  unfold tailWord_3735769
  simp only [CollatzResearch.WordTrace]
  refine ⟨136254689202954406395058361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90836459468636270930038907 136254689202954406395058361)
  ·
    refine ⟨102191016902215804796293771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136254689202954406395058361 102191016902215804796293771)
    ·
      refine ⟨153286525353323707194440657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102191016902215804796293771 153286525353323707194440657)
      ·
        refine ⟨114964894014992780395830493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 153286525353323707194440657 114964894014992780395830493)
        ·
          refine ⟨43111835255622292648436435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 114964894014992780395830493 43111835255622292648436435)
          ·
            refine ⟨64667752883433438972654653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43111835255622292648436435 64667752883433438972654653)
            ·
              refine ⟨24250407331287539614745495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64667752883433438972654653 24250407331287539614745495)
              ·
                refine ⟨36375610996931309422118243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24250407331287539614745495 36375610996931309422118243)
                ·
                  refine ⟨54563416495396964133177365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36375610996931309422118243 54563416495396964133177365)
                  ·
                    refine ⟨2557660148221732693742689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 54563416495396964133177365 2557660148221732693742689)
                    ·
                      refine ⟨1918245111166299520307017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2557660148221732693742689 1918245111166299520307017)
                      ·
                        rfl

theorem cell23_3735769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 3, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 3, 1, 1, 6, 2].length) (baseStart_3735769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3735769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3735769 prefixEnd_3735769 := by exact prefixLift 3735769
  have htrace : WordTrace (prefixWord ++ tailWord_3735769) baseStart_3735769 baseEnd_3735769 := by
    simpa [prefixWord, tailWord_3735769, baseEnd_3735769] using wordTrace_append hprefix tailTrace_3735769
  have hstable : (prefixWord ++ tailWord_3735769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3735769).length < 2 ^ (prefixWord ++ tailWord_3735769).sum := by decide
  have hdescent : baseEnd_3735769 < baseStart_3735769 := by decide
  rcases family_descends (prefixWord ++ tailWord_3735769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3735806 : List Nat := [4, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3]
def baseStart_3735806 : Nat := 118140960795 + 3735806 * 2 ^ 59
def prefixEnd_3735806 : Nat := 4983230072969 + 3 ^ 40 * 3735806 * 2
def baseEnd_3735806 : Nat := 1918264109950515875544347

theorem tailTrace_3735806 : CollatzResearch.WordTrace tailWord_3735806 prefixEnd_3735806 1918264109950515875544347 := by
  unfold tailWord_3735806
  simp only [CollatzResearch.WordTrace]
  refine ⟨17032004837977545214269409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 90837359135880241142770181 17032004837977545214269409)
  ·
    refine ⟨12774003628483158910702057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17032004837977545214269409 12774003628483158910702057)
    ·
      refine ⟨9580502721362369183026543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12774003628483158910702057 9580502721362369183026543)
      ·
        refine ⟨14370754082043553774539815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9580502721362369183026543 14370754082043553774539815)
        ·
          refine ⟨21556131123065330661809723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14370754082043553774539815 21556131123065330661809723)
          ·
            refine ⟨32334196684597995992714585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21556131123065330661809723 32334196684597995992714585)
            ·
              refine ⟨24250647513448496994535939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32334196684597995992714585 24250647513448496994535939)
              ·
                refine ⟨36375971270172745491803909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24250647513448496994535939 36375971270172745491803909)
                ·
                  refine ⟨6820494613157389779713233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36375971270172745491803909 6820494613157389779713233)
                  ·
                    refine ⟨5115370959868042334784925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6820494613157389779713233 5115370959868042334784925)
                    ·
                      refine ⟨1918264109950515875544347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5115370959868042334784925 1918264109950515875544347)
                      ·
                        rfl

theorem cell23_3735806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3].length) (baseStart_3735806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3735806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3735806 prefixEnd_3735806 := by exact prefixLift 3735806
  have htrace : WordTrace (prefixWord ++ tailWord_3735806) baseStart_3735806 baseEnd_3735806 := by
    simpa [prefixWord, tailWord_3735806, baseEnd_3735806] using wordTrace_append hprefix tailTrace_3735806
  have hstable : (prefixWord ++ tailWord_3735806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3735806).length < 2 ^ (prefixWord ++ tailWord_3735806).sum := by decide
  have hdescent : baseEnd_3735806 < baseStart_3735806 := by decide
  rcases family_descends (prefixWord ++ tailWord_3735806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3735870 : List Nat := [4, 2, 1, 2, 1, 4, 1, 1, 3, 1, 3]
def baseStart_3735870 : Nat := 118140960795 + 3735870 * 2 ^ 59
def prefixEnd_3735870 : Nat := 4983230072969 + 3 ^ 40 * 3735870 * 2
def baseEnd_3735870 : Nat := 1918296972712403625144053

theorem tailTrace_3735870 : CollatzResearch.WordTrace tailWord_3735870 prefixEnd_3735870 1918296972712403625144053 := by
  unfold tailWord_3735870
  simp only [CollatzResearch.WordTrace]
  refine ⟨17032296621948562580560633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 90838915317059000429656709 17032296621948562580560633)
  ·
    refine ⟨12774222466461421935420475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17032296621948562580560633 12774222466461421935420475)
    ·
      refine ⟨19161333699692132903130713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12774222466461421935420475 19161333699692132903130713)
      ·
        refine ⟨14371000274769099677348035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19161333699692132903130713 14371000274769099677348035)
        ·
          refine ⟨21556500412153649516022053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14371000274769099677348035 21556500412153649516022053)
          ·
            refine ⟨4041843827278809284254135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21556500412153649516022053 4041843827278809284254135)
            ·
              refine ⟨6062765740918213926381203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4041843827278809284254135 6062765740918213926381203)
              ·
                refine ⟨9094148611377320889571805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6062765740918213926381203 9094148611377320889571805)
                ·
                  refine ⟨3410305729266495333589427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9094148611377320889571805 3410305729266495333589427)
                  ·
                    refine ⟨5115458593899743000384141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3410305729266495333589427 5115458593899743000384141)
                    ·
                      refine ⟨1918296972712403625144053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5115458593899743000384141 1918296972712403625144053)
                      ·
                        rfl

theorem cell23_3735870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 4, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 4, 1, 1, 3, 1, 3].length) (baseStart_3735870 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3735870 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3735870 prefixEnd_3735870 := by exact prefixLift 3735870
  have htrace : WordTrace (prefixWord ++ tailWord_3735870) baseStart_3735870 baseEnd_3735870 := by
    simpa [prefixWord, tailWord_3735870, baseEnd_3735870] using wordTrace_append hprefix tailTrace_3735870
  have hstable : (prefixWord ++ tailWord_3735870).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3735870).length < 2 ^ (prefixWord ++ tailWord_3735870).sum := by decide
  have hdescent : baseEnd_3735870 < baseStart_3735870 := by decide
  rcases family_descends (prefixWord ++ tailWord_3735870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3735879 : List Nat := [1, 1, 4, 1, 2, 2, 1, 4, 1, 1, 5]
def baseStart_3735879 : Nat := 118140960795 + 3735879 * 2 ^ 59
def prefixEnd_3735879 : Nat := 4983230072969 + 3 ^ 40 * 3735879 * 2
def baseEnd_3735879 : Nat := 1918301594038294089931511

theorem tailTrace_3735879 : CollatzResearch.WordTrace tailWord_3735879 prefixEnd_3735879 1918301594038294089931511 := by
  unfold tailWord_3735879
  simp only [CollatzResearch.WordTrace]
  refine ⟨136258701232555895181562691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90839134155037263454375127 136258701232555895181562691)
  ·
    refine ⟨204388051848833842772344037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136258701232555895181562691 204388051848833842772344037)
    ·
      refine ⟨38322759721656345519814507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 204388051848833842772344037 38322759721656345519814507)
      ·
        refine ⟨57484139582484518279721761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38322759721656345519814507 57484139582484518279721761)
        ·
          refine ⟨43113104686863388709791321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57484139582484518279721761 43113104686863388709791321)
          ·
            refine ⟨32334828515147541532343491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43113104686863388709791321 32334828515147541532343491)
            ·
              refine ⟨48502242772721312298515237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32334828515147541532343491 48502242772721312298515237)
              ·
                refine ⟨9094170519885246055971607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48502242772721312298515237 9094170519885246055971607)
                ·
                  refine ⟨13641255779827869083957411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9094170519885246055971607 13641255779827869083957411)
                  ·
                    refine ⟨20461883669741803625936117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13641255779827869083957411 20461883669741803625936117)
                    ·
                      refine ⟨1918301594038294089931511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20461883669741803625936117 1918301594038294089931511)
                      ·
                        rfl

theorem cell23_3735879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 4, 1, 1, 5].length) (baseStart_3735879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3735879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3735879 prefixEnd_3735879 := by exact prefixLift 3735879
  have htrace : WordTrace (prefixWord ++ tailWord_3735879) baseStart_3735879 baseEnd_3735879 := by
    simpa [prefixWord, tailWord_3735879, baseEnd_3735879] using wordTrace_append hprefix tailTrace_3735879
  have hstable : (prefixWord ++ tailWord_3735879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3735879).length < 2 ^ (prefixWord ++ tailWord_3735879).sum := by decide
  have hdescent : baseEnd_3735879 < baseStart_3735879 := by decide
  rcases family_descends (prefixWord ++ tailWord_3735879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3735889 : List Nat := [1, 2, 2, 1, 4, 2, 2, 1, 1, 1, 6]
def baseStart_3735889 : Nat := 118140960795 + 3735889 * 2 ^ 59
def prefixEnd_3735889 : Nat := 4983230072969 + 3 ^ 40 * 3735889 * 2
def baseEnd_3735889 : Nat := 1918306728844839050806465

theorem tailTrace_3735889 : CollatzResearch.WordTrace tailWord_3735889 prefixEnd_3735889 1918306728844839050806465 := by
  unfold tailWord_3735889
  simp only [CollatzResearch.WordTrace]
  refine ⟨136259065962519666889426721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90839377308346444592951147 136259065962519666889426721)
  ·
    refine ⟨102194299471889750167070041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136259065962519666889426721 102194299471889750167070041)
    ·
      refine ⟨76645724603917312625302531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102194299471889750167070041 76645724603917312625302531)
      ·
        refine ⟨114968586905875968937953797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76645724603917312625302531 114968586905875968937953797)
        ·
          refine ⟨21556610044851744175866337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 114968586905875968937953797 21556610044851744175866337)
          ·
            refine ⟨16167457533638808131899753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21556610044851744175866337 16167457533638808131899753)
            ·
              refine ⟨12125593150229106098924815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16167457533638808131899753 12125593150229106098924815)
              ·
                refine ⟨18188389725343659148387223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12125593150229106098924815 18188389725343659148387223)
                ·
                  refine ⟨27282584588015488722580835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18188389725343659148387223 27282584588015488722580835)
                  ·
                    refine ⟨40923876882023233083871253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27282584588015488722580835 40923876882023233083871253)
                    ·
                      refine ⟨1918306728844839050806465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 40923876882023233083871253 1918306728844839050806465)
                      ·
                        rfl

theorem cell23_3735889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 2, 1, 1, 1, 6].length) (baseStart_3735889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3735889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3735889 prefixEnd_3735889 := by exact prefixLift 3735889
  have htrace : WordTrace (prefixWord ++ tailWord_3735889) baseStart_3735889 baseEnd_3735889 := by
    simpa [prefixWord, tailWord_3735889, baseEnd_3735889] using wordTrace_append hprefix tailTrace_3735889
  have hstable : (prefixWord ++ tailWord_3735889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3735889).length < 2 ^ (prefixWord ++ tailWord_3735889).sum := by decide
  have hdescent : baseEnd_3735889 < baseStart_3735889 := by decide
  rcases family_descends (prefixWord ++ tailWord_3735889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3735896 : List Nat := [2, 1, 2, 2, 1, 1, 2, 6, 1, 2, 3]
def baseStart_3735896 : Nat := 118140960795 + 3735896 * 2 ^ 59
def prefixEnd_3735896 : Nat := 4983230072969 + 3 ^ 40 * 3735896 * 2
def baseEnd_3735896 : Nat := 1918310323209420523418933

theorem tailTrace_3735896 : CollatzResearch.WordTrace tailWord_3735896 prefixEnd_3735896 1918310323209420523418933 := by
  unfold tailWord_3735896
  simp only [CollatzResearch.WordTrace]
  refine ⟨68129660636747153542465771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90839547515662871389954361 68129660636747153542465771)
  ·
    refine ⟨102194490955120730313698657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68129660636747153542465771 102194490955120730313698657)
    ·
      refine ⟨76645868216340547735273993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102194490955120730313698657 76645868216340547735273993)
      ·
        refine ⟨57484401162255410801455495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76645868216340547735273993 57484401162255410801455495)
        ·
          refine ⟨86226601743383116202183243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57484401162255410801455495 86226601743383116202183243)
          ·
            refine ⟨129339902615074674303274865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86226601743383116202183243 129339902615074674303274865)
            ·
              refine ⟨97004926961306005727456149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 129339902615074674303274865 97004926961306005727456149)
              ·
                refine ⟨4547105951311219018474507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 97004926961306005727456149 4547105951311219018474507)
                ·
                  refine ⟨6820658926966828527711761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4547105951311219018474507 6820658926966828527711761)
                  ·
                    refine ⟨5115494195225121395783821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6820658926966828527711761 5115494195225121395783821)
                    ·
                      refine ⟨1918310323209420523418933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5115494195225121395783821 1918310323209420523418933)
                      ·
                        rfl

theorem cell23_3735896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 6, 1, 2, 3].length) (baseStart_3735896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3735896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3735896 prefixEnd_3735896 := by exact prefixLift 3735896
  have htrace : WordTrace (prefixWord ++ tailWord_3735896) baseStart_3735896 baseEnd_3735896 := by
    simpa [prefixWord, tailWord_3735896, baseEnd_3735896] using wordTrace_append hprefix tailTrace_3735896
  have hstable : (prefixWord ++ tailWord_3735896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3735896).length < 2 ^ (prefixWord ++ tailWord_3735896).sum := by decide
  have hdescent : baseEnd_3735896 < baseStart_3735896 := by decide
  rcases family_descends (prefixWord ++ tailWord_3735896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3735906 : List Nat := [3, 3, 2, 1, 1, 2, 1, 1, 3, 2, 4]
def baseStart_3735906 : Nat := 118140960795 + 3735906 * 2 ^ 59
def prefixEnd_3735906 : Nat := 4983230072969 + 3 ^ 40 * 3735906 * 2
def baseEnd_3735906 : Nat := 1918315458015965484293887

theorem tailTrace_3735906 : CollatzResearch.WordTrace tailWord_3735906 prefixEnd_3735906 1918315458015965484293887 := by
  unfold tailWord_3735906
  simp only [CollatzResearch.WordTrace]
  refine ⟨34064921500864519698198893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90839790668972052528530381 34064921500864519698198893)
  ·
    refine ⟨12774345562824194886824585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34064921500864519698198893 12774345562824194886824585)
    ·
      refine ⟨9580759172118146165118439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12774345562824194886824585 9580759172118146165118439)
      ·
        refine ⟨14371138758177219247677659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9580759172118146165118439 14371138758177219247677659)
        ·
          refine ⟨21556708137265828871516489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14371138758177219247677659 21556708137265828871516489)
          ·
            refine ⟨16167531102949371653637367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21556708137265828871516489 16167531102949371653637367)
            ·
              refine ⟨24251296654424057480456051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16167531102949371653637367 24251296654424057480456051)
              ·
                refine ⟨36376944981636086220684077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24251296654424057480456051 36376944981636086220684077)
                ·
                  refine ⟨13641354368113532332756529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36376944981636086220684077 13641354368113532332756529)
                  ·
                    refine ⟨10231015776085149249567397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13641354368113532332756529 10231015776085149249567397)
                    ·
                      refine ⟨1918315458015965484293887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10231015776085149249567397 1918315458015965484293887)
                      ·
                        rfl

theorem cell23_3735906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 1, 1, 3, 2, 4].length) (baseStart_3735906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3735906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3735906 prefixEnd_3735906 := by exact prefixLift 3735906
  have htrace : WordTrace (prefixWord ++ tailWord_3735906) baseStart_3735906 baseEnd_3735906 := by
    simpa [prefixWord, tailWord_3735906, baseEnd_3735906] using wordTrace_append hprefix tailTrace_3735906
  have hstable : (prefixWord ++ tailWord_3735906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3735906).length < 2 ^ (prefixWord ++ tailWord_3735906).sum := by decide
  have hdescent : baseEnd_3735906 < baseStart_3735906 := by decide
  rcases family_descends (prefixWord ++ tailWord_3735906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3735913 : List Nat := [1, 2, 1, 1, 1, 3, 7, 1, 1, 2, 3]
def baseStart_3735913 : Nat := 118140960795 + 3735913 * 2 ^ 59
def prefixEnd_3735913 : Nat := 4983230072969 + 3 ^ 40 * 3735913 * 2
def baseEnd_3735913 : Nat := 1918319052380546956906355

theorem tailTrace_3735913 : CollatzResearch.WordTrace tailWord_3735913 prefixEnd_3735913 1918319052380546956906355 := by
  unfold tailWord_3735913
  simp only [CollatzResearch.WordTrace]
  refine ⟨136259941314432718988300393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90839960876288479325533595 136259941314432718988300393)
  ·
    refine ⟨102194955985824539241225295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136259941314432718988300393 102194955985824539241225295)
    ·
      refine ⟨153292433978736808861837943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102194955985824539241225295 153292433978736808861837943)
      ·
        refine ⟨229938650968105213292756915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153292433978736808861837943 229938650968105213292756915)
        ·
          refine ⟨344907976452157819939135373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 229938650968105213292756915 344907976452157819939135373)
          ·
            refine ⟨129340491169559182477175765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 344907976452157819939135373 129340491169559182477175765)
            ·
              refine ⟨3031417761786543339308807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 129340491169559182477175765 3031417761786543339308807)
              ·
                refine ⟨4547126642679815008963211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3031417761786543339308807 4547126642679815008963211)
                ·
                  refine ⟨6820689964019722513444817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4547126642679815008963211 6820689964019722513444817)
                  ·
                    refine ⟨5115517473014791885083613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6820689964019722513444817 5115517473014791885083613)
                    ·
                      refine ⟨1918319052380546956906355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5115517473014791885083613 1918319052380546956906355)
                      ·
                        rfl

theorem cell23_3735913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 7, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 7, 1, 1, 2, 3].length) (baseStart_3735913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3735913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3735913 prefixEnd_3735913 := by exact prefixLift 3735913
  have htrace : WordTrace (prefixWord ++ tailWord_3735913) baseStart_3735913 baseEnd_3735913 := by
    simpa [prefixWord, tailWord_3735913, baseEnd_3735913] using wordTrace_append hprefix tailTrace_3735913
  have hstable : (prefixWord ++ tailWord_3735913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3735913).length < 2 ^ (prefixWord ++ tailWord_3735913).sum := by decide
  have hdescent : baseEnd_3735913 < baseStart_3735913 := by decide
  rcases family_descends (prefixWord ++ tailWord_3735913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3735943 : List Nat := [1, 1, 4, 2, 2, 1, 1, 5, 2, 1, 3]
def baseStart_3735943 : Nat := 118140960795 + 3735943 * 2 ^ 59
def prefixEnd_3735943 : Nat := 4983230072969 + 3 ^ 40 * 3735943 * 2
def baseEnd_3735943 : Nat := 1918334456800181839531217

theorem tailTrace_3735943 : CollatzResearch.WordTrace tailWord_3735943 prefixEnd_3735943 1918334456800181839531217 := by
  unfold tailWord_3735943
  simp only [CollatzResearch.WordTrace]
  refine ⟨136261035504324034111892483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90840690336216022741261655 136261035504324034111892483)
  ·
    refine ⟨204391553256486051167838725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136261035504324034111892483 204391553256486051167838725)
    ·
      refine ⟨38323416235591134593969761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 204391553256486051167838725 38323416235591134593969761)
      ·
        refine ⟨28742562176693350945477321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38323416235591134593969761 28742562176693350945477321)
        ·
          refine ⟨21556921632520013209107991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28742562176693350945477321 21556921632520013209107991)
          ·
            refine ⟨32335382448780019813661987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21556921632520013209107991 32335382448780019813661987)
            ·
              refine ⟨48503073673170029720492981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32335382448780019813661987 48503073673170029720492981)
              ·
                refine ⟨4547163156859690286296217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 48503073673170029720492981 4547163156859690286296217)
                ·
                  refine ⟨3410372367644767714722163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4547163156859690286296217 3410372367644767714722163)
                  ·
                    refine ⟨5115558551467151572083245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3410372367644767714722163 5115558551467151572083245)
                    ·
                      refine ⟨1918334456800181839531217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5115558551467151572083245 1918334456800181839531217)
                      ·
                        rfl

theorem cell23_3735943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 5, 2, 1, 3].length) (baseStart_3735943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3735943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3735943 prefixEnd_3735943 := by exact prefixLift 3735943
  have htrace : WordTrace (prefixWord ++ tailWord_3735943) baseStart_3735943 baseEnd_3735943 := by
    simpa [prefixWord, tailWord_3735943, baseEnd_3735943] using wordTrace_append hprefix tailTrace_3735943
  have hstable : (prefixWord ++ tailWord_3735943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3735943).length < 2 ^ (prefixWord ++ tailWord_3735943).sum := by decide
  have hdescent : baseEnd_3735943 < baseStart_3735943 := by decide
  rcases family_descends (prefixWord ++ tailWord_3735943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3735970 : List Nat := [3, 3, 1, 2, 1, 1, 3, 3, 1, 3, 2]
def baseStart_3735970 : Nat := 118140960795 + 3735970 * 2 ^ 59
def prefixEnd_3735970 : Nat := 4983230072969 + 3 ^ 40 * 3735970 * 2
def baseEnd_3735970 : Nat := 1918348320777853233893593

theorem tailTrace_3735970 : CollatzResearch.WordTrace tailWord_3735970 prefixEnd_3735970 1918348320777853233893593 := by
  unfold tailWord_3735970
  simp only [CollatzResearch.WordTrace]
  refine ⟨34065505068806554430781341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90841346850150811815416909 34065505068806554430781341)
  ·
    refine ⟨12774564400802457911543003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34065505068806554430781341 12774564400802457911543003)
    ·
      refine ⟨19161846601203686867314505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12774564400802457911543003 19161846601203686867314505)
      ·
        refine ⟨14371384950902765150485879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19161846601203686867314505 14371384950902765150485879)
        ·
          refine ⟨21557077426354147725728819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14371384950902765150485879 21557077426354147725728819)
          ·
            refine ⟨32335616139531221588593229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21557077426354147725728819 32335616139531221588593229)
            ·
              refine ⟨12125856052324208095722461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32335616139531221588593229 12125856052324208095722461)
              ·
                refine ⟨4547196019621578035895923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12125856052324208095722461 4547196019621578035895923)
                ·
                  refine ⟨6820794029432367053843885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4547196019621578035895923 6820794029432367053843885)
                  ·
                    refine ⟨2557797761037137645191457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6820794029432367053843885 2557797761037137645191457)
                    ·
                      refine ⟨1918348320777853233893593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2557797761037137645191457 1918348320777853233893593)
                      ·
                        rfl

theorem cell23_3735970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 3, 3, 1, 3, 2].length) (baseStart_3735970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3735970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3735970 prefixEnd_3735970 := by exact prefixLift 3735970
  have htrace : WordTrace (prefixWord ++ tailWord_3735970) baseStart_3735970 baseEnd_3735970 := by
    simpa [prefixWord, tailWord_3735970, baseEnd_3735970] using wordTrace_append hprefix tailTrace_3735970
  have hstable : (prefixWord ++ tailWord_3735970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3735970).length < 2 ^ (prefixWord ++ tailWord_3735970).sum := by decide
  have hdescent : baseEnd_3735970 < baseStart_3735970 := by decide
  rcases family_descends (prefixWord ++ tailWord_3735970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3736040 : List Nat := [2, 1, 4, 1, 1, 4, 3, 2, 5]
def baseStart_3736040 : Nat := 118140960795 + 3736040 * 2 ^ 59
def prefixEnd_3736040 : Nat := 4983230072969 + 3 ^ 40 * 3736040 * 2
def baseEnd_3736040 : Nat := 213153807158185328890919

theorem tailTrace_3736040 : CollatzResearch.WordTrace tailWord_3736040 prefixEnd_3736040 213153807158185328890919 := by
  unfold tailWord_3736040
  simp only [CollatzResearch.WordTrace]
  refine ⟨68132286692486309839086787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90843048923315079785449049 68132286692486309839086787)
  ·
    refine ⟨102198430038729464758630181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68132286692486309839086787 102198430038729464758630181)
    ·
      refine ⟨19162205632261774642243159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 102198430038729464758630181 19162205632261774642243159)
      ·
        refine ⟨28743308448392661963364739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19162205632261774642243159 28743308448392661963364739)
        ·
          refine ⟨43114962672588992945047109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28743308448392661963364739 43114962672588992945047109)
          ·
            refine ⟨8084055501110436177196333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43114962672588992945047109 8084055501110436177196333)
            ·
              refine ⟨3031520812916413566448625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8084055501110436177196333 3031520812916413566448625)
              ·
                refine ⟨2273640609687310174836469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3031520812916413566448625 2273640609687310174836469)
                ·
                  refine ⟨213153807158185328890919, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2273640609687310174836469 213153807158185328890919)
                  ·
                    rfl

theorem cell23_3736040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 3, 2, 5].length) (baseStart_3736040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3736040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3736040 prefixEnd_3736040 := by exact prefixLift 3736040
  have htrace : WordTrace (prefixWord ++ tailWord_3736040) baseStart_3736040 baseEnd_3736040 := by
    simpa [prefixWord, tailWord_3736040, baseEnd_3736040] using wordTrace_append hprefix tailTrace_3736040
  have hstable : (prefixWord ++ tailWord_3736040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3736040).length < 2 ^ (prefixWord ++ tailWord_3736040).sum := by decide
  have hdescent : baseEnd_3736040 < baseStart_3736040 := by decide
  rcases family_descends (prefixWord ++ tailWord_3736040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3736046 : List Nat := [4, 1, 2, 1, 2, 2, 1, 1, 1, 1, 7]
def baseStart_3736046 : Nat := 118140960795 + 3736046 * 2 ^ 59
def prefixEnd_3736046 : Nat := 4983230072969 + 3 ^ 40 * 3736046 * 2
def baseEnd_3736046 : Nat := 1918387345307594936543243

theorem tailTrace_3736046 : CollatzResearch.WordTrace tailWord_3736046 prefixEnd_3736046 1918387345307594936543243 := by
  unfold tailWord_3736046
  simp only [CollatzResearch.WordTrace]
  refine ⟨17033099027868860337861499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 90843194815300588468594661 17033099027868860337861499)
  ·
    refine ⟨25549648541803290506792249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17033099027868860337861499 25549648541803290506792249)
    ·
      refine ⟨19162236406352467880094187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25549648541803290506792249 19162236406352467880094187)
      ·
        refine ⟨28743354609528701820141281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19162236406352467880094187 28743354609528701820141281)
        ·
          refine ⟨21557515957146526365105961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28743354609528701820141281 21557515957146526365105961)
          ·
            refine ⟨16168136967859894773829471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21557515957146526365105961 16168136967859894773829471)
            ·
              refine ⟨24252205451789842160744207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16168136967859894773829471 24252205451789842160744207)
              ·
                refine ⟨36378308177684763241116311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24252205451789842160744207 36378308177684763241116311)
                ·
                  refine ⟨54567462266527144861674467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36378308177684763241116311 54567462266527144861674467)
                  ·
                    refine ⟨81851193399790717292511701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 54567462266527144861674467 81851193399790717292511701)
                    ·
                      refine ⟨1918387345307594936543243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 81851193399790717292511701 1918387345307594936543243)
                      ·
                        rfl

theorem cell23_3736046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 1, 1, 1, 1, 7].length) (baseStart_3736046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3736046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3736046 prefixEnd_3736046 := by exact prefixLift 3736046
  have htrace : WordTrace (prefixWord ++ tailWord_3736046) baseStart_3736046 baseEnd_3736046 := by
    simpa [prefixWord, tailWord_3736046, baseEnd_3736046] using wordTrace_append hprefix tailTrace_3736046
  have hstable : (prefixWord ++ tailWord_3736046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3736046).length < 2 ^ (prefixWord ++ tailWord_3736046).sum := by decide
  have hdescent : baseEnd_3736046 < baseStart_3736046 := by decide
  rcases family_descends (prefixWord ++ tailWord_3736046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3736056 : List Nat := [2, 1, 2, 1, 1, 4, 1, 2, 4, 1, 4]
def baseStart_3736056 : Nat := 118140960795 + 3736056 * 2 ^ 59
def prefixEnd_3736056 : Nat := 4983230072969 + 3 ^ 40 * 3736056 * 2
def baseEnd_3736056 : Nat := 1918392480114139897418197

theorem tailTrace_3736056 : CollatzResearch.WordTrace tailWord_3736056 prefixEnd_3736056 1918392480114139897418197 := by
  unfold tailWord_3736056
  simp only [CollatzResearch.WordTrace]
  refine ⟨68132578476457327205378011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90843437968609769607170681 68132578476457327205378011)
  ·
    refine ⟨102198867714685990808067017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68132578476457327205378011 102198867714685990808067017)
    ·
      refine ⟨76649150786014493106050263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102198867714685990808067017 76649150786014493106050263)
      ·
        refine ⟨114973726179021739659075395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76649150786014493106050263 114973726179021739659075395)
        ·
          refine ⟨172460589268532609488613093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114973726179021739659075395 172460589268532609488613093)
          ·
            refine ⟨32336360487849864279114955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 172460589268532609488613093 32336360487849864279114955)
            ·
              refine ⟨48504540731774796418672433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32336360487849864279114955 48504540731774796418672433)
              ·
                refine ⟨36378405548831097314004325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48504540731774796418672433 36378405548831097314004325)
                ·
                  refine ⟨6820951040405830746375811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36378405548831097314004325 6820951040405830746375811)
                  ·
                    refine ⟨10231426560608746119563717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6820951040405830746375811 10231426560608746119563717)
                    ·
                      refine ⟨1918392480114139897418197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10231426560608746119563717 1918392480114139897418197)
                      ·
                        rfl

theorem cell23_3736056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 2, 4, 1, 4].length) (baseStart_3736056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3736056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3736056 prefixEnd_3736056 := by exact prefixLift 3736056
  have htrace : WordTrace (prefixWord ++ tailWord_3736056) baseStart_3736056 baseEnd_3736056 := by
    simpa [prefixWord, tailWord_3736056, baseEnd_3736056] using wordTrace_append hprefix tailTrace_3736056
  have hstable : (prefixWord ++ tailWord_3736056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3736056).length < 2 ^ (prefixWord ++ tailWord_3736056).sum := by decide
  have hdescent : baseEnd_3736056 < baseStart_3736056 := by decide
  rcases family_descends (prefixWord ++ tailWord_3736056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3736134 : List Nat := [6, 1, 1, 1, 2, 1, 1, 5, 1, 4]
def baseStart_3736134 : Nat := 118140960795 + 3736134 * 2 ^ 59
def prefixEnd_3736134 : Nat := 4983230072969 + 3 ^ 40 * 3736134 * 2
def baseEnd_3736134 : Nat := 639477510535063530747613

theorem tailTrace_3736134 : CollatzResearch.WordTrace tailWord_3736134 prefixEnd_3736134 639477510535063530747613 := by
  unfold tailWord_3736134
  simp only [CollatzResearch.WordTrace]
  refine ⟨4258375057707252304127983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 90845334564421382488063637 4258375057707252304127983)
  ·
    refine ⟨6387562586560878456191975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4258375057707252304127983 6387562586560878456191975)
    ·
      refine ⟨9581343879841317684287963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6387562586560878456191975 9581343879841317684287963)
      ·
        refine ⟨14372015819761976526431945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9581343879841317684287963 14372015819761976526431945)
        ·
          refine ⟨10779011864821482394823959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14372015819761976526431945 10779011864821482394823959)
          ·
            refine ⟨16168517797232223592235939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10779011864821482394823959 16168517797232223592235939)
            ·
              refine ⟨24252776695848335388353909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16168517797232223592235939 24252776695848335388353909)
              ·
                refine ⟨2273697815235781442658179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24252776695848335388353909 2273697815235781442658179)
                ·
                  refine ⟨3410546722853672163987269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2273697815235781442658179 3410546722853672163987269)
                  ·
                    refine ⟨639477510535063530747613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3410546722853672163987269 639477510535063530747613)
                    ·
                      rfl

theorem cell23_3736134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 1, 5, 1, 4].length) (baseStart_3736134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3736134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3736134 prefixEnd_3736134 := by exact prefixLift 3736134
  have htrace : WordTrace (prefixWord ++ tailWord_3736134) baseStart_3736134 baseEnd_3736134 := by
    simpa [prefixWord, tailWord_3736134, baseEnd_3736134] using wordTrace_append hprefix tailTrace_3736134
  have hstable : (prefixWord ++ tailWord_3736134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3736134).length < 2 ^ (prefixWord ++ tailWord_3736134).sum := by decide
  have hdescent : baseEnd_3736134 < baseStart_3736134 := by decide
  rcases family_descends (prefixWord ++ tailWord_3736134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3736183 : List Nat := [1, 1, 3, 1, 1, 3, 2, 3, 3, 2, 3]
def baseStart_3736183 : Nat := 118140960795 + 3736183 * 2 ^ 59
def prefixEnd_3736183 : Nat := 4983230072969 + 3 ^ 40 * 3736183 * 2
def baseEnd_3736183 : Nat := 1918457692157260900530113

theorem tailTrace_3736183 : CollatzResearch.WordTrace tailWord_3736183 prefixEnd_3736183 1918457692157260900530113 := by
  unfold tailWord_3736183
  simp only [CollatzResearch.WordTrace]
  refine ⟨136269789023454555100629203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90846526015636370067086135 136269789023454555100629203)
  ·
    refine ⟨204404683535181832650943805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136269789023454555100629203 204404683535181832650943805)
    ·
      refine ⟨76651756325693187244103927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 204404683535181832650943805 76651756325693187244103927)
      ·
        refine ⟨114977634488539780866155891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76651756325693187244103927 114977634488539780866155891)
        ·
          refine ⟨172466451732809671299233837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114977634488539780866155891 172466451732809671299233837)
          ·
            refine ⟨64674919399803626737212689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 172466451732809671299233837 64674919399803626737212689)
            ·
              refine ⟨48506189549852720052909517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64674919399803626737212689 48506189549852720052909517)
              ·
                refine ⟨18189821081194770019841069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48506189549852720052909517 18189821081194770019841069)
                ·
                  refine ⟨6821182905448038757440401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18189821081194770019841069 6821182905448038757440401)
                  ·
                    refine ⟨5115887179086029068080301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6821182905448038757440401 5115887179086029068080301)
                    ·
                      refine ⟨1918457692157260900530113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5115887179086029068080301 1918457692157260900530113)
                      ·
                        rfl

theorem cell23_3736183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 3, 3, 2, 3].length) (baseStart_3736183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3736183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3736183 prefixEnd_3736183 := by exact prefixLift 3736183
  have htrace : WordTrace (prefixWord ++ tailWord_3736183) baseStart_3736183 baseEnd_3736183 := by
    simpa [prefixWord, tailWord_3736183, baseEnd_3736183] using wordTrace_append hprefix tailTrace_3736183
  have hstable : (prefixWord ++ tailWord_3736183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3736183).length < 2 ^ (prefixWord ++ tailWord_3736183).sum := by decide
  have hdescent : baseEnd_3736183 < baseStart_3736183 := by decide
  rcases family_descends (prefixWord ++ tailWord_3736183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3736193 : List Nat := [1, 2, 4, 2, 1, 1, 2, 1, 3, 2, 4]
def baseStart_3736193 : Nat := 118140960795 + 3736193 * 2 ^ 59
def prefixEnd_3736193 : Nat := 4983230072969 + 3 ^ 40 * 3736193 * 2
def baseEnd_3736193 : Nat := 1918462826963805861405067

theorem tailTrace_3736193 : CollatzResearch.WordTrace tailWord_3736193 prefixEnd_3736193 1918462826963805861405067 := by
  unfold tailWord_3736193
  simp only [CollatzResearch.WordTrace]
  refine ⟨136270153753418326808493233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90846769168945551205662155 136270153753418326808493233)
  ·
    refine ⟨102202615315063745106369925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136270153753418326808493233 102202615315063745106369925)
    ·
      refine ⟨19162990371574452207444361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 102202615315063745106369925 19162990371574452207444361)
      ·
        refine ⟨14372242778680839155583271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19162990371574452207444361 14372242778680839155583271)
        ·
          refine ⟨21558364168021258733374907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14372242778680839155583271 21558364168021258733374907)
          ·
            refine ⟨32337546252031888100062361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21558364168021258733374907 32337546252031888100062361)
            ·
              refine ⟨24253159689023916075046771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32337546252031888100062361 24253159689023916075046771)
              ·
                refine ⟨36379739533535874112570157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24253159689023916075046771 36379739533535874112570157)
                ·
                  refine ⟨13642402325075952792213809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36379739533535874112570157 13642402325075952792213809)
                  ·
                    refine ⟨10231801743806964594160357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13642402325075952792213809 10231801743806964594160357)
                    ·
                      refine ⟨1918462826963805861405067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10231801743806964594160357 1918462826963805861405067)
                      ·
                        rfl

theorem cell23_3736193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 2, 1, 3, 2, 4].length) (baseStart_3736193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3736193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3736193 prefixEnd_3736193 := by exact prefixLift 3736193
  have htrace : WordTrace (prefixWord ++ tailWord_3736193) baseStart_3736193 baseEnd_3736193 := by
    simpa [prefixWord, tailWord_3736193, baseEnd_3736193] using wordTrace_append hprefix tailTrace_3736193
  have hstable : (prefixWord ++ tailWord_3736193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3736193).length < 2 ^ (prefixWord ++ tailWord_3736193).sum := by decide
  have hdescent : baseEnd_3736193 < baseStart_3736193 := by decide
  rcases family_descends (prefixWord ++ tailWord_3736193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3736224 : List Nat := [2, 1, 1, 4, 4, 2, 2, 1, 2, 4]
def baseStart_3736224 : Nat := 118140960795 + 3736224 * 2 ^ 59
def prefixEnd_3736224 : Nat := 4983230072969 + 3 ^ 40 * 3736224 * 2
def baseEnd_3736224 : Nat := 639492914954698413372475

theorem tailTrace_3736224 : CollatzResearch.WordTrace tailWord_3736224 prefixEnd_3736224 639492914954698413372475 := by
  unfold tailWord_3736224
  simp only [CollatzResearch.WordTrace]
  refine ⟨68135642208153009551435863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90847522944204012735247817 68135642208153009551435863)
  ·
    refine ⟨102203463312229514327153795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68135642208153009551435863 102203463312229514327153795)
    ·
      refine ⟨153305194968344271490730693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102203463312229514327153795 153305194968344271490730693)
      ·
        refine ⟨28744724056564550904512005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 153305194968344271490730693 28744724056564550904512005)
        ·
          refine ⟨5389635760605853294596001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28744724056564550904512005 5389635760605853294596001)
          ·
            refine ⟨4042226820454389970947001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5389635760605853294596001 4042226820454389970947001)
            ·
              refine ⟨3031670115340792478210251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4042226820454389970947001 3031670115340792478210251)
              ·
                refine ⟨4547505173011188717315377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3031670115340792478210251 4547505173011188717315377)
                ·
                  refine ⟨3410628879758391537986533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4547505173011188717315377 3410628879758391537986533)
                  ·
                    refine ⟨639492914954698413372475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3410628879758391537986533 639492914954698413372475)
                    ·
                      rfl

theorem cell23_3736224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 2, 2, 1, 2, 4].length) (baseStart_3736224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3736224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3736224 prefixEnd_3736224 := by exact prefixLift 3736224
  have htrace : WordTrace (prefixWord ++ tailWord_3736224) baseStart_3736224 baseEnd_3736224 := by
    simpa [prefixWord, tailWord_3736224, baseEnd_3736224] using wordTrace_append hprefix tailTrace_3736224
  have hstable : (prefixWord ++ tailWord_3736224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3736224).length < 2 ^ (prefixWord ++ tailWord_3736224).sum := by decide
  have hdescent : baseEnd_3736224 < baseStart_3736224 := by decide
  rcases family_descends (prefixWord ++ tailWord_3736224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3736231 : List Nat := [1, 1, 6, 3, 2, 1, 1, 2, 1, 1, 4]
def baseStart_3736231 : Nat := 118140960795 + 3736231 * 2 ^ 59
def prefixEnd_3736231 : Nat := 4983230072969 + 3 ^ 40 * 3736231 * 2
def baseEnd_3736231 : Nat := 1918482339228676712729893

theorem tailTrace_3736231 : CollatzResearch.WordTrace tailWord_3736231 prefixEnd_3736231 1918482339228676712729893 := by
  unfold tailWord_3736231
  simp only [CollatzResearch.WordTrace]
  refine ⟨136271539727280659298376547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90847693151520439532251031 136271539727280659298376547)
  ·
    refine ⟨204407309590920988947564821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136271539727280659298376547 204407309590920988947564821)
    ·
      refine ⟨9581592637074421356917101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 204407309590920988947564821 9581592637074421356917101)
      ·
        refine ⟨3593097238902908008843913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9581592637074421356917101 3593097238902908008843913)
        ·
          refine ⟨2694822929177181006632935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3593097238902908008843913 2694822929177181006632935)
          ·
            refine ⟨4042234393765771509949403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2694822929177181006632935 4042234393765771509949403)
            ·
              refine ⟨6063351590648657264924105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4042234393765771509949403 6063351590648657264924105)
              ·
                refine ⟨4547513692986492948693079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6063351590648657264924105 4547513692986492948693079)
                ·
                  refine ⟨6821270539479739423039619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4547513692986492948693079 6821270539479739423039619)
                  ·
                    refine ⟨10231905809219609134559429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6821270539479739423039619 10231905809219609134559429)
                    ·
                      refine ⟨1918482339228676712729893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10231905809219609134559429 1918482339228676712729893)
                      ·
                        rfl

theorem cell23_3736231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 2, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 2, 1, 1, 2, 1, 1, 4].length) (baseStart_3736231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3736231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3736231 prefixEnd_3736231 := by exact prefixLift 3736231
  have htrace : WordTrace (prefixWord ++ tailWord_3736231) baseStart_3736231 baseEnd_3736231 := by
    simpa [prefixWord, tailWord_3736231, baseEnd_3736231] using wordTrace_append hprefix tailTrace_3736231
  have hstable : (prefixWord ++ tailWord_3736231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3736231).length < 2 ^ (prefixWord ++ tailWord_3736231).sum := by decide
  have hdescent : baseEnd_3736231 < baseStart_3736231 := by decide
  rcases family_descends (prefixWord ++ tailWord_3736231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3736234 : List Nat := [3, 1, 5, 2, 1, 1, 1, 1, 3, 2, 3]
def baseStart_3736234 : Nat := 118140960795 + 3736234 * 2 ^ 59
def prefixEnd_3736234 : Nat := 4983230072969 + 3 ^ 40 * 3736234 * 2
def baseEnd_3736234 : Nat := 1918483879670640200992379

theorem tailTrace_3736234 : CollatzResearch.WordTrace tailWord_3736234 prefixEnd_3736234 1918483879670640200992379 := by
  unfold tailWord_3736234
  simp only [CollatzResearch.WordTrace]
  refine ⟨34067912286567447702683939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90847766097513193873823837 34067912286567447702683939)
  ·
    refine ⟨51101868429851171554025909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34067912286567447702683939 51101868429851171554025909)
    ·
      refine ⟨4790800165298547333189929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 51101868429851171554025909 4790800165298547333189929)
      ·
        refine ⟨3593100123973910499892447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4790800165298547333189929 3593100123973910499892447)
        ·
          refine ⟨5389650185960865749838671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3593100123973910499892447 5389650185960865749838671)
          ·
            refine ⟨8084475278941298624758007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5389650185960865749838671 8084475278941298624758007)
            ·
              refine ⟨12126712918411947937137011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8084475278941298624758007 12126712918411947937137011)
              ·
                refine ⟨18190069377617921905705517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12126712918411947937137011 18190069377617921905705517)
                ·
                  refine ⟨6821276016606720714639569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18190069377617921905705517 6821276016606720714639569)
                  ·
                    refine ⟨5115957012455040535979677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6821276016606720714639569 5115957012455040535979677)
                    ·
                      refine ⟨1918483879670640200992379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5115957012455040535979677 1918483879670640200992379)
                      ·
                        rfl

theorem cell23_3736234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 1, 1, 3, 2, 3].length) (baseStart_3736234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3736234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3736234 prefixEnd_3736234 := by exact prefixLift 3736234
  have htrace : WordTrace (prefixWord ++ tailWord_3736234) baseStart_3736234 baseEnd_3736234 := by
    simpa [prefixWord, tailWord_3736234, baseEnd_3736234] using wordTrace_append hprefix tailTrace_3736234
  have hstable : (prefixWord ++ tailWord_3736234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3736234).length < 2 ^ (prefixWord ++ tailWord_3736234).sum := by decide
  have hdescent : baseEnd_3736234 < baseStart_3736234 := by decide
  rcases family_descends (prefixWord ++ tailWord_3736234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3736273 : List Nat := [1, 2, 2, 1, 2, 3, 1, 1, 1, 6, 3]
def baseStart_3736273 : Nat := 118140960795 + 3736273 * 2 ^ 59
def prefixEnd_3736273 : Nat := 4983230072969 + 3 ^ 40 * 3736273 * 2
def baseEnd_3736273 : Nat := 1918503905416165548404699

theorem tailTrace_3736273 : CollatzResearch.WordTrace tailWord_3736273 prefixEnd_3736273 1918503905416165548404699 := by
  unfold tailWord_3736273
  simp only [CollatzResearch.WordTrace]
  refine ⟨136273071593128500471405473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90848714395419000314270315 136273071593128500471405473)
  ·
    refine ⟨102204803694846375353554105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136273071593128500471405473 102204803694846375353554105)
    ·
      refine ⟨76653602771134781515165579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102204803694846375353554105 76653602771134781515165579)
      ·
        refine ⟨114980404156702172272748369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76653602771134781515165579 114980404156702172272748369)
        ·
          refine ⟨86235303117526629204561277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114980404156702172272748369 86235303117526629204561277)
          ·
            refine ⟨32338238669072485951710479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 86235303117526629204561277 32338238669072485951710479)
            ·
              refine ⟨48507358003608728927565719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32338238669072485951710479 48507358003608728927565719)
              ·
                refine ⟨72761037005413093391348579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48507358003608728927565719 72761037005413093391348579)
                ·
                  refine ⟨109141555508119640087022869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 72761037005413093391348579 109141555508119640087022869)
                  ·
                    refine ⟨5116010414443108129079197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 109141555508119640087022869 5116010414443108129079197)
                    ·
                      refine ⟨1918503905416165548404699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5116010414443108129079197 1918503905416165548404699)
                      ·
                        rfl

theorem cell23_3736273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 1, 1, 6, 3].length) (baseStart_3736273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3736273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3736273 prefixEnd_3736273 := by exact prefixLift 3736273
  have htrace : WordTrace (prefixWord ++ tailWord_3736273) baseStart_3736273 baseEnd_3736273 := by
    simpa [prefixWord, tailWord_3736273, baseEnd_3736273] using wordTrace_append hprefix tailTrace_3736273
  have hstable : (prefixWord ++ tailWord_3736273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3736273).length < 2 ^ (prefixWord ++ tailWord_3736273).sum := by decide
  have hdescent : baseEnd_3736273 < baseStart_3736273 := by decide
  rcases family_descends (prefixWord ++ tailWord_3736273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3736287 : List Nat := [1, 1, 2, 3, 2, 4, 2, 1, 1, 4, 2]
def baseStart_3736287 : Nat := 118140960795 + 3736287 * 2 ^ 59
def prefixEnd_3736287 : Nat := 4983230072969 + 3 ^ 40 * 3736287 * 2
def baseEnd_3736287 : Nat := 1918511094145328493629635

theorem tailTrace_3736287 : CollatzResearch.WordTrace tailWord_3736287 prefixEnd_3736287 1918511094145328493629635 := by
  unfold tailWord_3736287
  simp only [CollatzResearch.WordTrace]
  refine ⟨136273582215077780862415115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90849054810051853908276743 136273582215077780862415115)
  ·
    refine ⟨204410373322616671293622673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136273582215077780862415115 204410373322616671293622673)
    ·
      refine ⟨153307779991962503470217005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 204410373322616671293622673 153307779991962503470217005)
      ·
        refine ⟨57490417496985938801331377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 153307779991962503470217005 57490417496985938801331377)
        ·
          refine ⟨43117813122739454100998533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57490417496985938801331377 43117813122739454100998533)
          ·
            refine ⟨8084589960513647643937225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43117813122739454100998533 8084589960513647643937225)
            ·
              refine ⟨6063442470385235732952919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8084589960513647643937225 6063442470385235732952919)
              ·
                refine ⟨9095163705577853599429379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6063442470385235732952919 9095163705577853599429379)
                ·
                  refine ⟨13642745558366780399144069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9095163705577853599429379 13642745558366780399144069)
                  ·
                    refine ⟨2558014792193771324839513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13642745558366780399144069 2558014792193771324839513)
                    ·
                      refine ⟨1918511094145328493629635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2558014792193771324839513 1918511094145328493629635)
                      ·
                        rfl

theorem cell23_3736287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 2, 1, 1, 4, 2].length) (baseStart_3736287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3736287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3736287 prefixEnd_3736287 := by exact prefixLift 3736287
  have htrace : WordTrace (prefixWord ++ tailWord_3736287) baseStart_3736287 baseEnd_3736287 := by
    simpa [prefixWord, tailWord_3736287, baseEnd_3736287] using wordTrace_append hprefix tailTrace_3736287
  have hstable : (prefixWord ++ tailWord_3736287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3736287).length < 2 ^ (prefixWord ++ tailWord_3736287).sum := by decide
  have hdescent : baseEnd_3736287 < baseStart_3736287 := by decide
  rcases family_descends (prefixWord ++ tailWord_3736287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3736293 : List Nat := [1, 3, 1, 4, 1, 2, 1, 1, 9]
def baseStart_3736293 : Nat := 118140960795 + 3736293 * 2 ^ 59
def prefixEnd_3736293 : Nat := 4983230072969 + 3 ^ 40 * 3736293 * 2
def baseEnd_3736293 : Nat := 213168241669917274461623

theorem tailTrace_3736293 : CollatzResearch.WordTrace tailWord_3736293 prefixEnd_3736293 213168241669917274461623 := by
  unfold tailWord_3736293
  simp only [CollatzResearch.WordTrace]
  refine ⟨136273801053056043887133533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90849200702037362591422355 136273801053056043887133533)
  ·
    refine ⟨51102675394896016457675075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 136273801053056043887133533 51102675394896016457675075)
    ·
      refine ⟨76654013092344024686512613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51102675394896016457675075 76654013092344024686512613)
      ·
        refine ⟨14372627454814504628721115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 76654013092344024686512613 14372627454814504628721115)
        ·
          refine ⟨21558941182221756943081673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14372627454814504628721115 21558941182221756943081673)
          ·
            refine ⟨16169205886666317707311255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21558941182221756943081673 16169205886666317707311255)
            ·
              refine ⟨24253808829999476560966883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16169205886666317707311255 24253808829999476560966883)
              ·
                refine ⟨36380713244999214841450325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24253808829999476560966883 36380713244999214841450325)
                ·
                  refine ⟨213168241669917274461623, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 36380713244999214841450325 213168241669917274461623)
                  ·
                    rfl

theorem cell23_3736293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 1, 1, 9].length) (baseStart_3736293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3736293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3736293 prefixEnd_3736293 := by exact prefixLift 3736293
  have htrace : WordTrace (prefixWord ++ tailWord_3736293) baseStart_3736293 baseEnd_3736293 := by
    simpa [prefixWord, tailWord_3736293, baseEnd_3736293] using wordTrace_append hprefix tailTrace_3736293
  have hstable : (prefixWord ++ tailWord_3736293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3736293).length < 2 ^ (prefixWord ++ tailWord_3736293).sum := by decide
  have hdescent : baseEnd_3736293 < baseStart_3736293 := by decide
  rcases family_descends (prefixWord ++ tailWord_3736293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3736308 : List Nat := [2, 6, 1, 1, 2, 1, 1, 3, 1, 3, 2]
def baseStart_3736308 : Nat := 118140960795 + 3736308 * 2 ^ 59
def prefixEnd_3736308 : Nat := 4983230072969 + 3 ^ 40 * 3736308 * 2
def baseEnd_3736308 : Nat := 1918521877239072911467039

theorem tailTrace_3736308 : CollatzResearch.WordTrace tailWord_3736308 prefixEnd_3736308 1918521877239072911467039 := by
  unfold tailWord_3736308
  simp only [CollatzResearch.WordTrace]
  refine ⟨68137174074000850724464789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90849565432001134299286385 68137174074000850724464789)
  ·
    refine ⟨3193930034718789877709287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 68137174074000850724464789 3193930034718789877709287)
    ·
      refine ⟨4790895052078184816563931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3193930034718789877709287 4790895052078184816563931)
      ·
        refine ⟨7186342578117277224845897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4790895052078184816563931 7186342578117277224845897)
        ·
          refine ⟨5389756933587957918634423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7186342578117277224845897 5389756933587957918634423)
          ·
            refine ⟨8084635400381936877951635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5389756933587957918634423 8084635400381936877951635)
            ·
              refine ⟨12126953100572905316927453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8084635400381936877951635 12126953100572905316927453)
              ·
                refine ⟨4547607412714839493847795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12126953100572905316927453 4547607412714839493847795)
                ·
                  refine ⟨6821411119072259240771693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4547607412714839493847795 6821411119072259240771693)
                  ·
                    refine ⟨2558029169652097215289385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6821411119072259240771693 2558029169652097215289385)
                    ·
                      refine ⟨1918521877239072911467039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2558029169652097215289385 1918521877239072911467039)
                      ·
                        rfl

theorem cell23_3736308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 1, 3, 1, 3, 2].length) (baseStart_3736308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3736308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3736308 prefixEnd_3736308 := by exact prefixLift 3736308
  have htrace : WordTrace (prefixWord ++ tailWord_3736308) baseStart_3736308 baseEnd_3736308 := by
    simpa [prefixWord, tailWord_3736308, baseEnd_3736308] using wordTrace_append hprefix tailTrace_3736308
  have hstable : (prefixWord ++ tailWord_3736308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3736308).length < 2 ^ (prefixWord ++ tailWord_3736308).sum := by decide
  have hdescent : baseEnd_3736308 < baseStart_3736308 := by decide
  rcases family_descends (prefixWord ++ tailWord_3736308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3736323 : List Nat := [1, 1, 1, 3, 2, 2, 1, 3, 4, 5]
def baseStart_3736323 : Nat := 118140960795 + 3736323 * 2 ^ 59
def prefixEnd_3736323 : Nat := 4983230072969 + 3 ^ 40 * 3736323 * 2
def baseEnd_3736323 : Nat := 639509859816296784259823

theorem tailTrace_3736323 : CollatzResearch.WordTrace tailWord_3736323 prefixEnd_3736323 639509859816296784259823 := by
  unfold tailWord_3736323
  simp only [CollatzResearch.WordTrace]
  refine ⟨136274895242947359010725623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90849930161964906007150415 136274895242947359010725623)
  ·
    refine ⟨204412342864421038516088435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136274895242947359010725623 204412342864421038516088435)
    ·
      refine ⟨306618514296631557774132653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204412342864421038516088435 306618514296631557774132653)
      ·
        refine ⟨114981942861236834165299745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 306618514296631557774132653 114981942861236834165299745)
        ·
          refine ⟨86236457145927625623974809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114981942861236834165299745 86236457145927625623974809)
          ·
            refine ⟨64677342859445719217981107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86236457145927625623974809 64677342859445719217981107)
            ·
              refine ⟨97016014289168578826971661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64677342859445719217981107 97016014289168578826971661)
              ·
                refine ⟨36381005358438217060114373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 97016014289168578826971661 36381005358438217060114373)
                ·
                  refine ⟨6821438504707165698771445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36381005358438217060114373 6821438504707165698771445)
                  ·
                    refine ⟨639509859816296784259823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6821438504707165698771445 639509859816296784259823)
                    ·
                      rfl

theorem cell23_3736323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 3, 4, 5].length) (baseStart_3736323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3736323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3736323 prefixEnd_3736323 := by exact prefixLift 3736323
  have htrace : WordTrace (prefixWord ++ tailWord_3736323) baseStart_3736323 baseEnd_3736323 := by
    simpa [prefixWord, tailWord_3736323, baseEnd_3736323] using wordTrace_append hprefix tailTrace_3736323
  have hstable : (prefixWord ++ tailWord_3736323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3736323).length < 2 ^ (prefixWord ++ tailWord_3736323).sum := by decide
  have hdescent : baseEnd_3736323 < baseStart_3736323 := by decide
  rcases family_descends (prefixWord ++ tailWord_3736323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3736327 : List Nat := [1, 1, 4, 4, 1, 1, 2, 4, 5]
def baseStart_3736327 : Nat := 118140960795 + 3736327 * 2 ^ 59
def prefixEnd_3736327 : Nat := 4983230072969 + 3 ^ 40 * 3736327 * 2
def baseEnd_3736327 : Nat := 213170181485723148569939

theorem tailTrace_3736327 : CollatzResearch.WordTrace tailWord_3736327 prefixEnd_3736327 213170181485723148569939 := by
  unfold tailWord_3736327
  simp only [CollatzResearch.WordTrace]
  refine ⟨136275041134932867693871235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90850027423288578462580823 136275041134932867693871235)
  ·
    refine ⟨204412561702399301540806853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136275041134932867693871235 204412561702399301540806853)
    ·
      refine ⟨38327355319199869038901285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 204412561702399301540806853 38327355319199869038901285)
      ·
        refine ⟨7186379122349975444793991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38327355319199869038901285 7186379122349975444793991)
        ·
          refine ⟨10779568683524963167190987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7186379122349975444793991 10779568683524963167190987)
          ·
            refine ⟨16169353025287444750786481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10779568683524963167190987 16169353025287444750786481)
            ·
              refine ⟨12127014768965583563089861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16169353025287444750786481 12127014768965583563089861)
              ·
                refine ⟨2273815269181046918079349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12127014768965583563089861 2273815269181046918079349)
                ·
                  refine ⟨213170181485723148569939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2273815269181046918079349 213170181485723148569939)
                  ·
                    rfl

theorem cell23_3736327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 2, 4, 5].length) (baseStart_3736327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3736327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3736327 prefixEnd_3736327 := by exact prefixLift 3736327
  have htrace : WordTrace (prefixWord ++ tailWord_3736327) baseStart_3736327 baseEnd_3736327 := by
    simpa [prefixWord, tailWord_3736327, baseEnd_3736327] using wordTrace_append hprefix tailTrace_3736327
  have hstable : (prefixWord ++ tailWord_3736327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3736327).length < 2 ^ (prefixWord ++ tailWord_3736327).sum := by decide
  have hdescent : baseEnd_3736327 < baseStart_3736327 := by decide
  rcases family_descends (prefixWord ++ tailWord_3736327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3736338 : List Nat := [3, 2, 4, 1, 3, 1, 1, 1, 1, 4, 2]
def baseStart_3736338 : Nat := 118140960795 + 3736338 * 2 ^ 59
def prefixEnd_3736338 : Nat := 4983230072969 + 3 ^ 40 * 3736338 * 2
def baseEnd_3736338 : Nat := 1918537281658707794091901

theorem tailTrace_3736338 : CollatzResearch.WordTrace tailWord_3736338 prefixEnd_3736338 1918537281658707794091901 := by
  unfold tailWord_3736338
  simp only [CollatzResearch.WordTrace]
  refine ⟨34068860584473254143130417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90850294891928677715014445 34068860584473254143130417)
  ·
    refine ⟨25551645438354940607347813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34068860584473254143130417 25551645438354940607347813)
    ·
      refine ⟨4790933519691551363877715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25551645438354940607347813 4790933519691551363877715)
      ·
        refine ⟨7186400279537327045816573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4790933519691551363877715 7186400279537327045816573)
        ·
          refine ⟨2694900104826497642181215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7186400279537327045816573 2694900104826497642181215)
          ·
            refine ⟨4042350157239746463271823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2694900104826497642181215 4042350157239746463271823)
            ·
              refine ⟨6063525235859619694907735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4042350157239746463271823 6063525235859619694907735)
              ·
                refine ⟨9095287853789429542361603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6063525235859619694907735 9095287853789429542361603)
                ·
                  refine ⟨13642931780684144313542405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9095287853789429542361603 13642931780684144313542405)
                  ·
                    refine ⟨2558049708878277058789201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13642931780684144313542405 2558049708878277058789201)
                    ·
                      refine ⟨1918537281658707794091901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2558049708878277058789201 1918537281658707794091901)
                      ·
                        rfl

theorem cell23_3736338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 3, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 3, 1, 1, 1, 1, 4, 2].length) (baseStart_3736338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3736338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3736338 prefixEnd_3736338 := by exact prefixLift 3736338
  have htrace : WordTrace (prefixWord ++ tailWord_3736338) baseStart_3736338 baseEnd_3736338 := by
    simpa [prefixWord, tailWord_3736338, baseEnd_3736338] using wordTrace_append hprefix tailTrace_3736338
  have hstable : (prefixWord ++ tailWord_3736338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3736338).length < 2 ^ (prefixWord ++ tailWord_3736338).sum := by decide
  have hdescent : baseEnd_3736338 < baseStart_3736338 := by decide
  rcases family_descends (prefixWord ++ tailWord_3736338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3736353 : List Nat := [1, 2, 3, 2, 1, 2, 1, 1, 2, 8]
def baseStart_3736353 : Nat := 118140960795 + 3736353 * 2 ^ 59
def prefixEnd_3736353 : Nat := 4983230072969 + 3 ^ 40 * 3736353 * 2
def baseEnd_3736353 : Nat := 639514994622841745134777

theorem tailTrace_3736353 : CollatzResearch.WordTrace tailWord_3736353 prefixEnd_3736353 639514994622841745134777 := by
  unfold tailWord_3736353
  simp only [CollatzResearch.WordTrace]
  refine ⟨136275989432838674134317713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90850659621892449422878475 136275989432838674134317713)
  ·
    refine ⟨102206992074629005600738285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136275989432838674134317713 102206992074629005600738285)
    ·
      refine ⟨38327622027985877100276857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102206992074629005600738285 38327622027985877100276857)
      ·
        refine ⟨28745716520989407825207643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38327622027985877100276857 28745716520989407825207643)
        ·
          refine ⟨43118574781484111737811465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28745716520989407825207643 43118574781484111737811465)
          ·
            refine ⟨32338931086113083803358599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43118574781484111737811465 32338931086113083803358599)
            ·
              refine ⟨48508396629169625705037899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32338931086113083803358599 48508396629169625705037899)
              ·
                refine ⟨72762594943754438557556849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48508396629169625705037899 72762594943754438557556849)
                ·
                  refine ⟨54571946207815828918167637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 72762594943754438557556849 54571946207815828918167637)
                  ·
                    refine ⟨639514994622841745134777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 54571946207815828918167637 639514994622841745134777)
                    ·
                      rfl

theorem cell23_3736353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 1, 2, 8].length) (baseStart_3736353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3736353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3736353 prefixEnd_3736353 := by exact prefixLift 3736353
  have htrace : WordTrace (prefixWord ++ tailWord_3736353) baseStart_3736353 baseEnd_3736353 := by
    simpa [prefixWord, tailWord_3736353, baseEnd_3736353] using wordTrace_append hprefix tailTrace_3736353
  have hstable : (prefixWord ++ tailWord_3736353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3736353).length < 2 ^ (prefixWord ++ tailWord_3736353).sum := by decide
  have hdescent : baseEnd_3736353 < baseStart_3736353 := by decide
  rcases family_descends (prefixWord ++ tailWord_3736353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3736360 : List Nat := [2, 1, 5, 1, 1, 1, 1, 3, 1, 3, 4]
def baseStart_3736360 : Nat := 118140960795 + 3736360 * 2 ^ 59
def prefixEnd_3736360 : Nat := 4983230072969 + 3 ^ 40 * 3736360 * 2
def baseEnd_3736360 : Nat := 1918548578233106708016799

theorem tailTrace_3736360 : CollatzResearch.WordTrace tailWord_3736360 prefixEnd_3736360 1918548578233106708016799 := by
  unfold tailWord_3736360
  simp only [CollatzResearch.WordTrace]
  refine ⟨68138122371906657164911267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90850829829208876219881689 68138122371906657164911267)
  ·
    refine ⟨102207183557859985747366901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68138122371906657164911267 102207183557859985747366901)
    ·
      refine ⟨9581923458549373663815647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 102207183557859985747366901 9581923458549373663815647)
      ·
        refine ⟨14372885187824060495723471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9581923458549373663815647 14372885187824060495723471)
        ·
          refine ⟨21559327781736090743585207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14372885187824060495723471 21559327781736090743585207)
          ·
            refine ⟨32338991672604136115377811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21559327781736090743585207 32338991672604136115377811)
            ·
              refine ⟨48508487508906204173066717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32338991672604136115377811 48508487508906204173066717)
              ·
                refine ⟨18190682815839826564900019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48508487508906204173066717 18190682815839826564900019)
                ·
                  refine ⟨27286024223759739847350029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18190682815839826564900019 27286024223759739847350029)
                  ·
                    refine ⟨10232259083909902442756261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27286024223759739847350029 10232259083909902442756261)
                    ·
                      refine ⟨1918548578233106708016799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10232259083909902442756261 1918548578233106708016799)
                      ·
                        rfl

theorem cell23_3736360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 3, 1, 3, 4].length) (baseStart_3736360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3736360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3736360 prefixEnd_3736360 := by exact prefixLift 3736360
  have htrace : WordTrace (prefixWord ++ tailWord_3736360) baseStart_3736360 baseEnd_3736360 := by
    simpa [prefixWord, tailWord_3736360, baseEnd_3736360] using wordTrace_append hprefix tailTrace_3736360
  have hstable : (prefixWord ++ tailWord_3736360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3736360).length < 2 ^ (prefixWord ++ tailWord_3736360).sum := by decide
  have hdescent : baseEnd_3736360 < baseStart_3736360 := by decide
  rcases family_descends (prefixWord ++ tailWord_3736360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3736374 : List Nat := [5, 1, 2, 2, 2, 1, 1, 2, 2, 5]
def baseStart_3736374 : Nat := 118140960795 + 3736374 * 2 ^ 59
def prefixEnd_3736374 : Nat := 4983230072969 + 3 ^ 40 * 3736374 * 2
def baseEnd_3736374 : Nat := 639518588987423217747245

theorem tailTrace_3736374 : CollatzResearch.WordTrace tailWord_3736374 prefixEnd_3736374 639518588987423217747245 := by
  unfold tailWord_3736374
  simp only [CollatzResearch.WordTrace]
  refine ⟨8517297210360162170052011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 90851170243841729813888117 8517297210360162170052011)
  ·
    refine ⟨12775945815540243255078017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8517297210360162170052011 12775945815540243255078017)
    ·
      refine ⟨9581959361655182441308513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12775945815540243255078017 9581959361655182441308513)
      ·
        refine ⟨7186469521241386830981385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9581959361655182441308513 7186469521241386830981385)
        ·
          refine ⟨5389852140931040123236039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7186469521241386830981385 5389852140931040123236039)
          ·
            refine ⟨8084778211396560184854059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5389852140931040123236039 8084778211396560184854059)
            ·
              refine ⟨12127167317094840277281089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8084778211396560184854059 12127167317094840277281089)
              ·
                refine ⟨9095375487821130207960817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12127167317094840277281089 9095375487821130207960817)
                ·
                  refine ⟨6821531615865847655970613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9095375487821130207960817 6821531615865847655970613)
                  ·
                    refine ⟨639518588987423217747245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6821531615865847655970613 639518588987423217747245)
                    ·
                      rfl

theorem cell23_3736374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 1, 2, 2, 5].length) (baseStart_3736374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3736374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3736374 prefixEnd_3736374 := by exact prefixLift 3736374
  have htrace : WordTrace (prefixWord ++ tailWord_3736374) baseStart_3736374 baseEnd_3736374 := by
    simpa [prefixWord, tailWord_3736374, baseEnd_3736374] using wordTrace_append hprefix tailTrace_3736374
  have hstable : (prefixWord ++ tailWord_3736374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3736374).length < 2 ^ (prefixWord ++ tailWord_3736374).sum := by decide
  have hdescent : baseEnd_3736374 < baseStart_3736374 := by decide
  rcases family_descends (prefixWord ++ tailWord_3736374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3736403 : List Nat := [1, 1, 1, 2, 1, 1, 3, 4, 1, 2, 6]
def baseStart_3736403 : Nat := 118140960795 + 3736403 * 2 ^ 59
def prefixEnd_3736403 : Nat := 4983230072969 + 3 ^ 40 * 3736403 * 2
def baseEnd_3736403 : Nat := 1918570657901250039779101

theorem tailTrace_3736403 : CollatzResearch.WordTrace tailWord_3736403 prefixEnd_3736403 1918570657901250039779101 := by
  unfold tailWord_3736403
  simp only [CollatzResearch.WordTrace]
  refine ⟨136277813082657532673637863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90851875388438355115758575 136277813082657532673637863)
  ·
    refine ⟨204416719623986299010456795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136277813082657532673637863 204416719623986299010456795)
    ·
      refine ⟨306625079435979448515685193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204416719623986299010456795 306625079435979448515685193)
      ·
        refine ⟨229968809576984586386763895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 306625079435979448515685193 229968809576984586386763895)
        ·
          refine ⟨344953214365476879580145843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 229968809576984586386763895 344953214365476879580145843)
          ·
            refine ⟨517429821548215319370218765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 344953214365476879580145843 517429821548215319370218765)
            ·
              refine ⟨194036183080580744763832037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 517429821548215319370218765 194036183080580744763832037)
              ·
                refine ⟨36381784327608889643218507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 194036183080580744763832037 36381784327608889643218507)
                ·
                  refine ⟨54572676491413334464827761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36381784327608889643218507 54572676491413334464827761)
                  ·
                    refine ⟨40929507368560000848620821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 54572676491413334464827761 40929507368560000848620821)
                    ·
                      refine ⟨1918570657901250039779101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 40929507368560000848620821 1918570657901250039779101)
                      ·
                        rfl

theorem cell23_3736403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 4, 1, 2, 6].length) (baseStart_3736403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3736403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3736403 prefixEnd_3736403 := by exact prefixLift 3736403
  have htrace : WordTrace (prefixWord ++ tailWord_3736403) baseStart_3736403 baseEnd_3736403 := by
    simpa [prefixWord, tailWord_3736403, baseEnd_3736403] using wordTrace_append hprefix tailTrace_3736403
  have hstable : (prefixWord ++ tailWord_3736403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3736403).length < 2 ^ (prefixWord ++ tailWord_3736403).sum := by decide
  have hdescent : baseEnd_3736403 < baseStart_3736403 := by decide
  rcases family_descends (prefixWord ++ tailWord_3736403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3736438 : List Nat := [5, 1, 1, 3, 1, 1, 4, 2, 1, 4]
def baseStart_3736438 : Nat := 118140960795 + 3736438 * 2 ^ 59
def prefixEnd_3736438 : Nat := 4983230072969 + 3 ^ 40 * 3736438 * 2
def baseEnd_3736438 : Nat := 639529543241385800947147

theorem tailTrace_3736438 : CollatzResearch.WordTrace tailWord_3736438 prefixEnd_3736438 639529543241385800947147 := by
  unfold tailWord_3736438
  simp only [CollatzResearch.WordTrace]
  refine ⟨8517443102345670853197623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 90852726425020489100774645 8517443102345670853197623)
  ·
    refine ⟨12776164653518506279796435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8517443102345670853197623 12776164653518506279796435)
    ·
      refine ⟨19164246980277759419694653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12776164653518506279796435 19164246980277759419694653)
      ·
        refine ⟨7186592617604159782385495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19164246980277759419694653 7186592617604159782385495)
        ·
          refine ⟨10779888926406239673578243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7186592617604159782385495 10779888926406239673578243)
          ·
            refine ⟨16169833389609359510367365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10779888926406239673578243 16169833389609359510367365)
            ·
              refine ⟨3031843760551754908193881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16169833389609359510367365 3031843760551754908193881)
              ·
                refine ⟨2273882820413816181145411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3031843760551754908193881 2273882820413816181145411)
                ·
                  refine ⟨3410824230620724271718117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2273882820413816181145411 3410824230620724271718117)
                  ·
                    refine ⟨639529543241385800947147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3410824230620724271718117 639529543241385800947147)
                    ·
                      rfl

theorem cell23_3736438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 4, 2, 1, 4].length) (baseStart_3736438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3736438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3736438 prefixEnd_3736438 := by exact prefixLift 3736438
  have htrace : WordTrace (prefixWord ++ tailWord_3736438) baseStart_3736438 baseEnd_3736438 := by
    simpa [prefixWord, tailWord_3736438, baseEnd_3736438] using wordTrace_append hprefix tailTrace_3736438
  have hstable : (prefixWord ++ tailWord_3736438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3736438).length < 2 ^ (prefixWord ++ tailWord_3736438).sum := by decide
  have hdescent : baseEnd_3736438 < baseStart_3736438 := by decide
  rcases family_descends (prefixWord ++ tailWord_3736438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3736460 : List Nat := [2, 2, 1, 2, 1, 2, 3, 3, 1, 6]
def baseStart_3736460 : Nat := 118140960795 + 3736460 * 2 ^ 59
def prefixEnd_3736460 : Nat := 4983230072969 + 3 ^ 40 * 3736460 * 2
def baseEnd_3736460 : Nat := 639533308766185438922113

theorem tailTrace_3736460 : CollatzResearch.WordTrace tailWord_3736460 prefixEnd_3736460 639533308766185438922113 := by
  unfold tailWord_3736460
  simp only [CollatzResearch.WordTrace]
  refine ⟨68139946021725515704231417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90853261362300687605641889 68139946021725515704231417)
  ·
    refine ⟨51104959516294136778173563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68139946021725515704231417 51104959516294136778173563)
    ·
      refine ⟨76657439274441205167260345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51104959516294136778173563 76657439274441205167260345)
      ·
        refine ⟨57493079455830903875445259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76657439274441205167260345 57493079455830903875445259)
        ·
          refine ⟨86239619183746355813167889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57493079455830903875445259 86239619183746355813167889)
          ·
            refine ⟨64679714387809766859875917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86239619183746355813167889 64679714387809766859875917)
            ·
              refine ⟨24254892895428662572453469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64679714387809766859875917 24254892895428662572453469)
              ·
                refine ⟨9095584835785748464670051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24254892895428662572453469 9095584835785748464670051)
                ·
                  refine ⟨13643377253678622697005077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9095584835785748464670051 13643377253678622697005077)
                  ·
                    refine ⟨639533308766185438922113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13643377253678622697005077 639533308766185438922113)
                    ·
                      rfl

theorem cell23_3736460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 3, 3, 1, 6].length) (baseStart_3736460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3736460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3736460 prefixEnd_3736460 := by exact prefixLift 3736460
  have htrace : WordTrace (prefixWord ++ tailWord_3736460) baseStart_3736460 baseEnd_3736460 := by
    simpa [prefixWord, tailWord_3736460, baseEnd_3736460] using wordTrace_append hprefix tailTrace_3736460
  have hstable : (prefixWord ++ tailWord_3736460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3736460).length < 2 ^ (prefixWord ++ tailWord_3736460).sum := by decide
  have hdescent : baseEnd_3736460 < baseStart_3736460 := by decide
  rcases family_descends (prefixWord ++ tailWord_3736460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3736477 : List Nat := [1, 4, 2, 1, 2, 1, 2, 2, 4, 4]
def baseStart_3736477 : Nat := 118140960795 + 3736477 * 2 ^ 59
def prefixEnd_3736477 : Nat := 4983230072969 + 3 ^ 40 * 3736477 * 2
def baseEnd_3736477 : Nat := 639536218489894250084587

theorem tailTrace_3736477 : CollatzResearch.WordTrace tailWord_3736477 prefixEnd_3736477 639536218489894250084587 := by
  unfold tailWord_3736477
  simp only [CollatzResearch.WordTrace]
  refine ⟨136280512084389443311831685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90853674722926295541221123 136280512084389443311831685)
  ·
    refine ⟨25552596015823020620968441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 136280512084389443311831685 25552596015823020620968441)
    ·
      refine ⟨19164447011867265465726331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25552596015823020620968441 19164447011867265465726331)
      ·
        refine ⟨28746670517800898198589497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19164447011867265465726331 28746670517800898198589497)
        ·
          refine ⟨21560002888350673648942123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28746670517800898198589497 21560002888350673648942123)
          ·
            refine ⟨32340004332526010473413185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21560002888350673648942123 32340004332526010473413185)
            ·
              refine ⟨24255003249394507855059889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32340004332526010473413185 24255003249394507855059889)
              ·
                refine ⟨18191252437045880891294917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24255003249394507855059889 18191252437045880891294917)
                ·
                  refine ⟨3410859831946102667117797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18191252437045880891294917 3410859831946102667117797)
                  ·
                    refine ⟨639536218489894250084587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3410859831946102667117797 639536218489894250084587)
                    ·
                      rfl

theorem cell23_3736477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 2, 2, 4, 4].length) (baseStart_3736477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3736477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3736477 prefixEnd_3736477 := by exact prefixLift 3736477
  have htrace : WordTrace (prefixWord ++ tailWord_3736477) baseStart_3736477 baseEnd_3736477 := by
    simpa [prefixWord, tailWord_3736477, baseEnd_3736477] using wordTrace_append hprefix tailTrace_3736477
  have hstable : (prefixWord ++ tailWord_3736477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3736477).length < 2 ^ (prefixWord ++ tailWord_3736477).sum := by decide
  have hdescent : baseEnd_3736477 < baseStart_3736477 := by decide
  rcases family_descends (prefixWord ++ tailWord_3736477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3736481 : List Nat := [1, 2, 3, 4, 1, 3, 2, 1, 1, 5]
def baseStart_3736481 : Nat := 118140960795 + 3736481 * 2 ^ 59
def prefixEnd_3736481 : Nat := 4983230072969 + 3 ^ 40 * 3736481 * 2
def baseEnd_3736481 : Nat := 639536903130766911534581

theorem tailTrace_3736481 : CollatzResearch.WordTrace tailWord_3736481 prefixEnd_3736481 639536903130766911534581 := by
  unfold tailWord_3736481
  simp only [CollatzResearch.WordTrace]
  refine ⟨136280657976374951994977297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90853771984249967996651531 136280657976374951994977297)
  ·
    refine ⟨102210493482281213996232973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136280657976374951994977297 102210493482281213996232973)
    ·
      refine ⟨38328935055855455248587365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102210493482281213996232973 38328935055855455248587365)
      ·
        refine ⟨7186675322972897859110131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38328935055855455248587365 7186675322972897859110131)
        ·
          refine ⟨10780012984459346788665197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7186675322972897859110131 10780012984459346788665197)
          ·
            refine ⟨4042504869172255045749449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10780012984459346788665197 4042504869172255045749449)
            ·
              refine ⟨3031878651879191284312087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4042504869172255045749449 3031878651879191284312087)
              ·
                refine ⟨4547817977818786926468131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3031878651879191284312087 4547817977818786926468131)
                ·
                  refine ⟨6821726966728180389702197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4547817977818786926468131 6821726966728180389702197)
                  ·
                    refine ⟨639536903130766911534581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6821726966728180389702197 639536903130766911534581)
                    ·
                      rfl

theorem cell23_3736481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 3, 2, 1, 1, 5].length) (baseStart_3736481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3736481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3736481 prefixEnd_3736481 := by exact prefixLift 3736481
  have htrace : WordTrace (prefixWord ++ tailWord_3736481) baseStart_3736481 baseEnd_3736481 := by
    simpa [prefixWord, tailWord_3736481, baseEnd_3736481] using wordTrace_append hprefix tailTrace_3736481
  have hstable : (prefixWord ++ tailWord_3736481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3736481).length < 2 ^ (prefixWord ++ tailWord_3736481).sum := by decide
  have hdescent : baseEnd_3736481 < baseStart_3736481 := by decide
  rcases family_descends (prefixWord ++ tailWord_3736481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3736484 : List Nat := [2, 3, 1, 2, 1, 2, 1, 2, 5, 2, 2]
def baseStart_3736484 : Nat := 118140960795 + 3736484 * 2 ^ 59
def prefixEnd_3736484 : Nat := 4983230072969 + 3 ^ 40 * 3736484 * 2
def baseEnd_3736484 : Nat := 1918612249834264222866229

theorem tailTrace_3736484 : CollatzResearch.WordTrace tailWord_3736484 prefixEnd_3736484 1918612249834264222866229 := by
  unfold tailWord_3736484
  simp only [CollatzResearch.WordTrace]
  refine ⟨68140383697682041753668253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90853844930242722338224337 68140383697682041753668253)
  ·
    refine ⟨25552643886630765657625595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68140383697682041753668253 25552643886630765657625595)
    ·
      refine ⟨38328965829946148486438393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25552643886630765657625595 38328965829946148486438393)
      ·
        refine ⟨28746724372459611364828795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38328965829946148486438393 28746724372459611364828795)
        ·
          refine ⟨43120086558689417047243193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28746724372459611364828795 43120086558689417047243193)
          ·
            refine ⟨32340064919017062785432395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43120086558689417047243193 32340064919017062785432395)
            ·
              refine ⟨48510097378525594178148593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32340064919017062785432395 48510097378525594178148593)
              ·
                refine ⟨36382573033894195633611445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48510097378525594178148593 36382573033894195633611445)
                ·
                  refine ⟨3410866221927580840651073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 36382573033894195633611445 3410866221927580840651073)
                  ·
                    refine ⟨2558149666445685630488305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3410866221927580840651073 2558149666445685630488305)
                    ·
                      refine ⟨1918612249834264222866229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2558149666445685630488305 1918612249834264222866229)
                      ·
                        rfl

theorem cell23_3736484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 2, 5, 2, 2].length) (baseStart_3736484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3736484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3736484 prefixEnd_3736484 := by exact prefixLift 3736484
  have htrace : WordTrace (prefixWord ++ tailWord_3736484) baseStart_3736484 baseEnd_3736484 := by
    simpa [prefixWord, tailWord_3736484, baseEnd_3736484] using wordTrace_append hprefix tailTrace_3736484
  have hstable : (prefixWord ++ tailWord_3736484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3736484).length < 2 ^ (prefixWord ++ tailWord_3736484).sum := by decide
  have hdescent : baseEnd_3736484 < baseStart_3736484 := by decide
  rcases family_descends (prefixWord ++ tailWord_3736484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3736501 : List Nat := [1, 3, 3, 2, 1, 1, 4, 1, 3, 2, 2]
def baseStart_3736501 : Nat := 118140960795 + 3736501 * 2 ^ 59
def prefixEnd_3736501 : Nat := 4983230072969 + 3 ^ 40 * 3736501 * 2
def baseEnd_3736501 : Nat := 1918620979005390656353651

theorem tailTrace_3736501 : CollatzResearch.WordTrace tailWord_3736501 prefixEnd_3736501 1918620979005390656353651 := by
  unfold tailWord_3736501
  simp only [CollatzResearch.WordTrace]
  refine ⟨136281387436302495410705357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90854258290868330273803571 136281387436302495410705357)
  ·
    refine ⟨51105520288613435779014509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 136281387436302495410705357 51105520288613435779014509)
    ·
      refine ⟨19164570108230038417130441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51105520288613435779014509 19164570108230038417130441)
      ·
        refine ⟨14373427581172528812847831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19164570108230038417130441 14373427581172528812847831)
        ·
          refine ⟨21560141371758793219271747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14373427581172528812847831 21560141371758793219271747)
          ·
            refine ⟨32340212057638189828907621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21560141371758793219271747 32340212057638189828907621)
            ·
              refine ⟨6063789760807160592920179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32340212057638189828907621 6063789760807160592920179)
              ·
                refine ⟨9095684641210740889380269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6063789760807160592920179 9095684641210740889380269)
                ·
                  refine ⟨3410881740454027833517601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9095684641210740889380269 3410881740454027833517601)
                  ·
                    refine ⟨2558161305340520875138201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3410881740454027833517601 2558161305340520875138201)
                    ·
                      refine ⟨1918620979005390656353651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2558161305340520875138201 1918620979005390656353651)
                      ·
                        rfl

theorem cell23_3736501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 4, 1, 3, 2, 2].length) (baseStart_3736501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3736501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3736501 prefixEnd_3736501 := by exact prefixLift 3736501
  have htrace : WordTrace (prefixWord ++ tailWord_3736501) baseStart_3736501 baseEnd_3736501 := by
    simpa [prefixWord, tailWord_3736501, baseEnd_3736501] using wordTrace_append hprefix tailTrace_3736501
  have hstable : (prefixWord ++ tailWord_3736501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3736501).length < 2 ^ (prefixWord ++ tailWord_3736501).sum := by decide
  have hdescent : baseEnd_3736501 < baseStart_3736501 := by decide
  rcases family_descends (prefixWord ++ tailWord_3736501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3736560 : List Nat := [2, 1, 1, 1, 3, 2, 1, 1, 3, 3, 5]
def baseStart_3736560 : Nat := 118140960795 + 3736560 * 2 ^ 59
def prefixEnd_3736560 : Nat := 4983230072969 + 3 ^ 40 * 3736560 * 2
def baseEnd_3736560 : Nat := 1918651274364005925515879

theorem tailTrace_3736560 : CollatzResearch.WordTrace tailWord_3736560 prefixEnd_3736560 1918651274364005925515879 := by
  unfold tailWord_3736560
  simp only [CollatzResearch.WordTrace]
  refine ⟨68141769671544374243551567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90855692895392498991402089 68141769671544374243551567)
  ·
    refine ⟨102212654507316561365327351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68141769671544374243551567 102212654507316561365327351)
    ·
      refine ⟨153318981760974842047991027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102212654507316561365327351 153318981760974842047991027)
      ·
        refine ⟨229978472641462263071986541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153318981760974842047991027 229978472641462263071986541)
        ·
          refine ⟨86241927240548348651994953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 229978472641462263071986541 86241927240548348651994953)
          ·
            refine ⟨64681445430411261488996215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86241927240548348651994953 64681445430411261488996215)
            ·
              refine ⟨97022168145616892233494323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64681445430411261488996215 97022168145616892233494323)
              ·
                refine ⟨145533252218425338350241485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 97022168145616892233494323 145533252218425338350241485)
                ·
                  refine ⟨54574969581909501881340557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 145533252218425338350241485 54574969581909501881340557)
                  ·
                    refine ⟨20465613593216063205502709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 54574969581909501881340557 20465613593216063205502709)
                    ·
                      refine ⟨1918651274364005925515879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20465613593216063205502709 1918651274364005925515879)
                      ·
                        rfl

theorem cell23_3736560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 1, 3, 3, 5].length) (baseStart_3736560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3736560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3736560 prefixEnd_3736560 := by exact prefixLift 3736560
  have htrace : WordTrace (prefixWord ++ tailWord_3736560) baseStart_3736560 baseEnd_3736560 := by
    simpa [prefixWord, tailWord_3736560, baseEnd_3736560] using wordTrace_append hprefix tailTrace_3736560
  have hstable : (prefixWord ++ tailWord_3736560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3736560).length < 2 ^ (prefixWord ++ tailWord_3736560).sum := by decide
  have hdescent : baseEnd_3736560 < baseStart_3736560 := by decide
  rcases family_descends (prefixWord ++ tailWord_3736560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3736570 : List Nat := [3, 1, 1, 1, 1, 2, 1, 2, 2, 3, 6]
def baseStart_3736570 : Nat := 118140960795 + 3736570 * 2 ^ 59
def prefixEnd_3736570 : Nat := 4983230072969 + 3 ^ 40 * 3736570 * 2
def baseEnd_3736570 : Nat := 1918656409170550886390833

theorem tailTrace_3736570 : CollatzResearch.WordTrace tailWord_3736570 prefixEnd_3736570 1918656409170550886390833 := by
  unfold tailWord_3736570
  simp only [CollatzResearch.WordTrace]
  refine ⟨34070976018263130048741791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90855936048701680129978109 34070976018263130048741791)
  ·
    refine ⟨51106464027394695073112687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34070976018263130048741791 51106464027394695073112687)
    ·
      refine ⟨76659696041092042609669031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51106464027394695073112687 76659696041092042609669031)
      ·
        refine ⟨114989544061638063914503547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76659696041092042609669031 114989544061638063914503547)
        ·
          refine ⟨172484316092457095871755321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114989544061638063914503547 172484316092457095871755321)
          ·
            refine ⟨129363237069342821903816491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 172484316092457095871755321 129363237069342821903816491)
            ·
              refine ⟨194044855604014232855724737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 129363237069342821903816491 194044855604014232855724737)
              ·
                refine ⟨145533641703010674641793553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 194044855604014232855724737 145533641703010674641793553)
                ·
                  refine ⟨109150231277258005981345165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 145533641703010674641793553 109150231277258005981345165)
                  ·
                    refine ⟨40931336728971752243004437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 109150231277258005981345165 40931336728971752243004437)
                    ·
                      refine ⟨1918656409170550886390833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 40931336728971752243004437 1918656409170550886390833)
                      ·
                        rfl

theorem cell23_3736570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 2, 2, 3, 6].length) (baseStart_3736570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3736570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3736570 prefixEnd_3736570 := by exact prefixLift 3736570
  have htrace : WordTrace (prefixWord ++ tailWord_3736570) baseStart_3736570 baseEnd_3736570 := by
    simpa [prefixWord, tailWord_3736570, baseEnd_3736570] using wordTrace_append hprefix tailTrace_3736570
  have hstable : (prefixWord ++ tailWord_3736570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3736570).length < 2 ^ (prefixWord ++ tailWord_3736570).sum := by decide
  have hdescent : baseEnd_3736570 < baseStart_3736570 := by decide
  rcases family_descends (prefixWord ++ tailWord_3736570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3736577 : List Nat := [1, 2, 4, 1, 2, 2, 1, 2, 2, 1, 5]
def baseStart_3736577 : Nat := 118140960795 + 3736577 * 2 ^ 59
def prefixEnd_3736577 : Nat := 4983230072969 + 3 ^ 40 * 3736577 * 2
def baseEnd_3736577 : Nat := 1918660003535132359003301

theorem tailTrace_3736577 : CollatzResearch.WordTrace tailWord_3736577 prefixEnd_3736577 1918660003535132359003301 := by
  unfold tailWord_3736577
  simp only [CollatzResearch.WordTrace]
  refine ⟨136284159384027160390471985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90856106256018106926981323 136284159384027160390471985)
  ·
    refine ⟨102213119538020370292853989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136284159384027160390471985 102213119538020370292853989)
    ·
      refine ⟨19164959913378819429910123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 102213119538020370292853989 19164959913378819429910123)
      ·
        refine ⟨28747439870068229144865185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19164959913378819429910123 28747439870068229144865185)
        ·
          refine ⟨21560579902551171858648889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28747439870068229144865185 21560579902551171858648889)
          ·
            refine ⟨16170434926913378893986667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21560579902551171858648889 16170434926913378893986667)
            ·
              refine ⟨24255652390370068340980001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16170434926913378893986667 24255652390370068340980001)
              ·
                refine ⟨18191739292777551255735001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24255652390370068340980001 18191739292777551255735001)
                ·
                  refine ⟨13643804469583163441801251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18191739292777551255735001 13643804469583163441801251)
                  ·
                    refine ⟨20465706704374745162701877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13643804469583163441801251 20465706704374745162701877)
                    ·
                      refine ⟨1918660003535132359003301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20465706704374745162701877 1918660003535132359003301)
                      ·
                        rfl

theorem cell23_3736577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 1, 2, 2, 1, 5].length) (baseStart_3736577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3736577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3736577 prefixEnd_3736577 := by exact prefixLift 3736577
  have htrace : WordTrace (prefixWord ++ tailWord_3736577) baseStart_3736577 baseEnd_3736577 := by
    simpa [prefixWord, tailWord_3736577, baseEnd_3736577] using wordTrace_append hprefix tailTrace_3736577
  have hstable : (prefixWord ++ tailWord_3736577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3736577).length < 2 ^ (prefixWord ++ tailWord_3736577).sum := by decide
  have hdescent : baseEnd_3736577 < baseStart_3736577 := by decide
  rcases family_descends (prefixWord ++ tailWord_3736577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3736664 : List Nat := [2, 1, 2, 2, 1, 3, 1, 1, 4, 4, 2]
def baseStart_3736664 : Nat := 118140960795 + 3736664 * 2 ^ 59
def prefixEnd_3736664 : Nat := 4983230072969 + 3 ^ 40 * 3736664 * 2
def baseEnd_3736664 : Nat := 1918704676352073518615401

theorem tailTrace_3736664 : CollatzResearch.WordTrace tailWord_3736664 prefixEnd_3736664 1918704676352073518615401 := by
  unfold tailWord_3736664
  simp only [CollatzResearch.WordTrace]
  refine ⟨68143666267355987124444523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90858221689807982832592697 68143666267355987124444523)
  ·
    refine ⟨102215499401033980686666785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68143666267355987124444523 102215499401033980686666785)
    ·
      refine ⟨76661624550775485515000089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102215499401033980686666785 76661624550775485515000089)
      ·
        refine ⟨57496218413081614136250067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76661624550775485515000089 57496218413081614136250067)
        ·
          refine ⟨86244327619622421204375101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57496218413081614136250067 86244327619622421204375101)
          ·
            refine ⟨32341622857358407951640663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 86244327619622421204375101 32341622857358407951640663)
            ·
              refine ⟨48512434286037611927460995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32341622857358407951640663 48512434286037611927460995)
              ·
                refine ⟨72768651429056417891191493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48512434286037611927460995 72768651429056417891191493)
                ·
                  refine ⟨13644122142948078354598405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 72768651429056417891191493 13644122142948078354598405)
                  ·
                    refine ⟨2558272901802764691487201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13644122142948078354598405 2558272901802764691487201)
                    ·
                      refine ⟨1918704676352073518615401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2558272901802764691487201 1918704676352073518615401)
                      ·
                        rfl

theorem cell23_3736664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 1, 4, 4, 2].length) (baseStart_3736664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3736664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3736664 prefixEnd_3736664 := by exact prefixLift 3736664
  have htrace : WordTrace (prefixWord ++ tailWord_3736664) baseStart_3736664 baseEnd_3736664 := by
    simpa [prefixWord, tailWord_3736664, baseEnd_3736664] using wordTrace_append hprefix tailTrace_3736664
  have hstable : (prefixWord ++ tailWord_3736664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3736664).length < 2 ^ (prefixWord ++ tailWord_3736664).sum := by decide
  have hdescent : baseEnd_3736664 < baseStart_3736664 := by decide
  rcases family_descends (prefixWord ++ tailWord_3736664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3736677 : List Nat := [1, 3, 1, 3, 2, 1, 1, 2, 2, 1, 6]
def baseStart_3736677 : Nat := 118140960795 + 3736677 * 2 ^ 59
def prefixEnd_3736677 : Nat := 4983230072969 + 3 ^ 40 * 3736677 * 2
def baseEnd_3736677 : Nat := 1918711351600581967752841

theorem tailTrace_3736677 : CollatzResearch.WordTrace tailWord_3736677 prefixEnd_3736677 1918711351600581967752841 := by
  unfold tailWord_3736677
  simp only [CollatzResearch.WordTrace]
  refine ⟨136287806683664877469112285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90858537789109918312741523 136287806683664877469112285)
  ·
    refine ⟨51107927506374329050917107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 136287806683664877469112285 51107927506374329050917107)
    ·
      refine ⟨76661891259561493576375661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51107927506374329050917107 76661891259561493576375661)
      ·
        refine ⟨28748209222335560091140873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76661891259561493576375661 28748209222335560091140873)
        ·
          refine ⟨21561156916751670068355655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28748209222335560091140873 21561156916751670068355655)
          ·
            refine ⟨32341735375127505102533483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21561156916751670068355655 32341735375127505102533483)
            ·
              refine ⟨48512603062691257653800225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32341735375127505102533483 48512603062691257653800225)
              ·
                refine ⟨36384452297018443240350169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48512603062691257653800225 36384452297018443240350169)
                ·
                  refine ⟨27288339222763832430262627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36384452297018443240350169 27288339222763832430262627)
                  ·
                    refine ⟨40932508834145748645393941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27288339222763832430262627 40932508834145748645393941)
                    ·
                      refine ⟨1918711351600581967752841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 40932508834145748645393941 1918711351600581967752841)
                      ·
                        rfl

theorem cell23_3736677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 2, 2, 1, 6].length) (baseStart_3736677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3736677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3736677 prefixEnd_3736677 := by exact prefixLift 3736677
  have htrace : WordTrace (prefixWord ++ tailWord_3736677) baseStart_3736677 baseEnd_3736677 := by
    simpa [prefixWord, tailWord_3736677, baseEnd_3736677] using wordTrace_append hprefix tailTrace_3736677
  have hstable : (prefixWord ++ tailWord_3736677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3736677).length < 2 ^ (prefixWord ++ tailWord_3736677).sum := by decide
  have hdescent : baseEnd_3736677 < baseStart_3736677 := by decide
  rcases family_descends (prefixWord ++ tailWord_3736677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3736694 : List Nat := [5, 1, 1, 2, 1, 1, 1, 1, 2, 4, 4]
def baseStart_3736694 : Nat := 118140960795 + 3736694 * 2 ^ 59
def prefixEnd_3736694 : Nat := 4983230072969 + 3 ^ 40 * 3736694 * 2
def baseEnd_3736694 : Nat := 1918720080771708401240263

theorem tailTrace_3736694 : CollatzResearch.WordTrace tailWord_3736694 prefixEnd_3736694 1918720080771708401240263 := by
  unfold tailWord_3736694
  simp only [CollatzResearch.WordTrace]
  refine ⟨8518026670287705585780071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 90858951149735526248320757 8518026670287705585780071)
  ·
    refine ⟨12777040005431558378670107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8518026670287705585780071 12777040005431558378670107)
    ·
      refine ⟨19165560008147337568005161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12777040005431558378670107 19165560008147337568005161)
      ·
        refine ⟨14374170006110503176003871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19165560008147337568005161 14374170006110503176003871)
        ·
          refine ⟨21561255009165754764005807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14374170006110503176003871 21561255009165754764005807)
          ·
            refine ⟨32341882513748632146008711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21561255009165754764005807 32341882513748632146008711)
            ·
              refine ⟨48512823770622948219013067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32341882513748632146008711 48512823770622948219013067)
              ·
                refine ⟨72769235655934422328519601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48512823770622948219013067 72769235655934422328519601)
                ·
                  refine ⟨54576926741950816746389701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 72769235655934422328519601 54576926741950816746389701)
                  ·
                    refine ⟨10233173764115778139948069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 54576926741950816746389701 10233173764115778139948069)
                    ·
                      refine ⟨1918720080771708401240263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10233173764115778139948069 1918720080771708401240263)
                      ·
                        rfl

theorem cell23_3736694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 1, 2, 4, 4].length) (baseStart_3736694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3736694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3736694 prefixEnd_3736694 := by exact prefixLift 3736694
  have htrace : WordTrace (prefixWord ++ tailWord_3736694) baseStart_3736694 baseEnd_3736694 := by
    simpa [prefixWord, tailWord_3736694, baseEnd_3736694] using wordTrace_append hprefix tailTrace_3736694
  have hstable : (prefixWord ++ tailWord_3736694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3736694).length < 2 ^ (prefixWord ++ tailWord_3736694).sum := by decide
  have hdescent : baseEnd_3736694 < baseStart_3736694 := by decide
  rcases family_descends (prefixWord ++ tailWord_3736694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3736708 : List Nat := [2, 3, 2, 1, 2, 2, 3, 3, 1, 4]
def baseStart_3736708 : Nat := 118140960795 + 3736708 * 2 ^ 59
def prefixEnd_3736708 : Nat := 4983230072969 + 3 ^ 40 * 3736708 * 2
def baseEnd_3736708 : Nat := 639575756500290448821733

theorem tailTrace_3736708 : CollatzResearch.WordTrace tailWord_3736708 prefixEnd_3736708 639575756500290448821733 := by
  unfold tailWord_3736708
  simp only [CollatzResearch.WordTrace]
  refine ⟨68144468673276284881745389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90859291564368379842327185 68144468673276284881745389)
  ·
    refine ⟨25554175752478606830654521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68144468673276284881745389 25554175752478606830654521)
    ·
      refine ⟨19165631814358955122990891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25554175752478606830654521 19165631814358955122990891)
      ·
        refine ⟨28748447721538432684486337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19165631814358955122990891 28748447721538432684486337)
        ·
          refine ⟨21561335791153824513364753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28748447721538432684486337 21561335791153824513364753)
          ·
            refine ⟨16171001843365368385023565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21561335791153824513364753 16171001843365368385023565)
            ·
              refine ⟨6064125691262013144383837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16171001843365368385023565 6064125691262013144383837)
              ·
                refine ⟨2274047134223254929143939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6064125691262013144383837 2274047134223254929143939)
                ·
                  refine ⟨3411070701334882393715909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2274047134223254929143939 3411070701334882393715909)
                  ·
                    refine ⟨639575756500290448821733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3411070701334882393715909 639575756500290448821733)
                    ·
                      rfl

theorem cell23_3736708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 3, 3, 1, 4].length) (baseStart_3736708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3736708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3736708 prefixEnd_3736708 := by exact prefixLift 3736708
  have htrace : WordTrace (prefixWord ++ tailWord_3736708) baseStart_3736708 baseEnd_3736708 := by
    simpa [prefixWord, tailWord_3736708, baseEnd_3736708] using wordTrace_append hprefix tailTrace_3736708
  have hstable : (prefixWord ++ tailWord_3736708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3736708).length < 2 ^ (prefixWord ++ tailWord_3736708).sum := by decide
  have hdescent : baseEnd_3736708 < baseStart_3736708 := by decide
  rcases family_descends (prefixWord ++ tailWord_3736708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3736764 : List Nat := [2, 2, 2, 3, 2, 1, 1, 1, 3, 6]
def baseStart_3736764 : Nat := 118140960795 + 3736764 * 2 ^ 59
def prefixEnd_3736764 : Nat := 4983230072969 + 3 ^ 40 * 3736764 * 2
def baseEnd_3736764 : Nat := 639585341472507709121647

theorem tailTrace_3736764 : CollatzResearch.WordTrace tailWord_3736764 prefixEnd_3736764 639585341472507709121647 := by
  unfold tailWord_3736764
  simp only [CollatzResearch.WordTrace]
  refine ⟨68145489917174845663764673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90860653222899794218352897 68145489917174845663764673)
  ·
    refine ⟨51109117437881134247823505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68145489917174845663764673 51109117437881134247823505)
    ·
      refine ⟨38331838078410850685867629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51109117437881134247823505 38331838078410850685867629)
      ·
        refine ⟨14374439279404069007200361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38331838078410850685867629 14374439279404069007200361)
        ·
          refine ⟨10780829459553051755400271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14374439279404069007200361 10780829459553051755400271)
          ·
            refine ⟨16171244189329577633100407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10780829459553051755400271 16171244189329577633100407)
            ·
              refine ⟨24256866283994366449650611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16171244189329577633100407 24256866283994366449650611)
              ·
                refine ⟨36385299425991549674475917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24256866283994366449650611 36385299425991549674475917)
                ·
                  refine ⟨13644487284746831127928469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36385299425991549674475917 13644487284746831127928469)
                  ·
                    refine ⟨639585341472507709121647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13644487284746831127928469 639585341472507709121647)
                    ·
                      rfl

theorem cell23_3736764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 1, 1, 3, 6].length) (baseStart_3736764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3736764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3736764 prefixEnd_3736764 := by exact prefixLift 3736764
  have htrace : WordTrace (prefixWord ++ tailWord_3736764) baseStart_3736764 baseEnd_3736764 := by
    simpa [prefixWord, tailWord_3736764, baseEnd_3736764] using wordTrace_append hprefix tailTrace_3736764
  have hstable : (prefixWord ++ tailWord_3736764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3736764).length < 2 ^ (prefixWord ++ tailWord_3736764).sum := by decide
  have hdescent : baseEnd_3736764 < baseStart_3736764 := by decide
  rcases family_descends (prefixWord ++ tailWord_3736764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3736768 : List Nat := [2, 1, 1, 2, 6, 1, 3, 1, 1, 5]
def baseStart_3736768 : Nat := 118140960795 + 3736768 * 2 ^ 59
def prefixEnd_3736768 : Nat := 4983230072969 + 3 ^ 40 * 3736768 * 2
def baseEnd_3736768 : Nat := 639586026113380370571641

theorem tailTrace_3736768 : CollatzResearch.WordTrace tailWord_3736768 prefixEnd_3736768 639586026113380370571641 := by
  unfold tailWord_3736768
  simp only [CollatzResearch.WordTrace]
  refine ⟨68145562863167600005337479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90860750484223466673783305 68145562863167600005337479)
  ·
    refine ⟨102218344294751400008006219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68145562863167600005337479 102218344294751400008006219)
    ·
      refine ⟨153327516442127100012009329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102218344294751400008006219 153327516442127100012009329)
      ·
        refine ⟨114995637331595325009006997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 153327516442127100012009329 114995637331595325009006997)
        ·
          refine ⟨5390420499918530859797203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 114995637331595325009006997 5390420499918530859797203)
          ·
            refine ⟨8085630749877796289695805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5390420499918530859797203 8085630749877796289695805)
            ·
              refine ⟨3032111531204173608635927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8085630749877796289695805 3032111531204173608635927)
              ·
                refine ⟨4548167296806260412953891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3032111531204173608635927 4548167296806260412953891)
                ·
                  refine ⟨6822250945209390619430837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4548167296806260412953891 6822250945209390619430837)
                  ·
                    refine ⟨639586026113380370571641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6822250945209390619430837 639586026113380370571641)
                    ·
                      rfl

theorem cell23_3736768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 3, 1, 1, 5].length) (baseStart_3736768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3736768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3736768 prefixEnd_3736768 := by exact prefixLift 3736768
  have htrace : WordTrace (prefixWord ++ tailWord_3736768) baseStart_3736768 baseEnd_3736768 := by
    simpa [prefixWord, tailWord_3736768, baseEnd_3736768] using wordTrace_append hprefix tailTrace_3736768
  have hstable : (prefixWord ++ tailWord_3736768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3736768).length < 2 ^ (prefixWord ++ tailWord_3736768).sum := by decide
  have hdescent : baseEnd_3736768 < baseStart_3736768 := by decide
  rcases family_descends (prefixWord ++ tailWord_3736768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3736771 : List Nat := [1, 1, 1, 3, 1, 1, 1, 3, 7, 2, 2]
def baseStart_3736771 : Nat := 118140960795 + 3736771 * 2 ^ 59
def prefixEnd_3736771 : Nat := 4983230072969 + 3 ^ 40 * 3736771 * 2
def baseEnd_3736771 : Nat := 1918759618782104599977409

theorem tailTrace_3736771 : CollatzResearch.WordTrace tailWord_3736771 prefixEnd_3736771 1918759618782104599977409 := by
  unfold tailWord_3736771
  simp only [CollatzResearch.WordTrace]
  refine ⟨136291235145324331523034167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90860823430216221015356111 136291235145324331523034167)
  ·
    refine ⟨204436852717986497284551251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136291235145324331523034167 204436852717986497284551251)
    ·
      refine ⟨306655279076979745926826877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204436852717986497284551251 306655279076979745926826877)
      ·
        refine ⟨114995729653867404722560079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 306655279076979745926826877 114995729653867404722560079)
        ·
          refine ⟨172493594480801107083840119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114995729653867404722560079 172493594480801107083840119)
          ·
            refine ⟨258740391721201660625760179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 172493594480801107083840119 258740391721201660625760179)
            ·
              refine ⟨388110587581802490938640269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 258740391721201660625760179 388110587581802490938640269)
              ·
                refine ⟨145541470343175934101990101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 388110587581802490938640269 145541470343175934101990101)
                ·
                  refine ⟨3411128211168185955515393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 145541470343175934101990101 3411128211168185955515393)
                  ·
                    refine ⟨2558346158376139466636545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3411128211168185955515393 2558346158376139466636545)
                    ·
                      refine ⟨1918759618782104599977409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2558346158376139466636545 1918759618782104599977409)
                      ·
                        rfl

theorem cell23_3736771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 3, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 3, 7, 2, 2].length) (baseStart_3736771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3736771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3736771 prefixEnd_3736771 := by exact prefixLift 3736771
  have htrace : WordTrace (prefixWord ++ tailWord_3736771) baseStart_3736771 baseEnd_3736771 := by
    simpa [prefixWord, tailWord_3736771, baseEnd_3736771] using wordTrace_append hprefix tailTrace_3736771
  have hstable : (prefixWord ++ tailWord_3736771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3736771).length < 2 ^ (prefixWord ++ tailWord_3736771).sum := by decide
  have hdescent : baseEnd_3736771 < baseStart_3736771 := by decide
  rcases family_descends (prefixWord ++ tailWord_3736771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3736801 : List Nat := [1, 2, 3, 1, 3, 3, 2, 1, 1, 2, 4]
def baseStart_3736801 : Nat := 118140960795 + 3736801 * 2 ^ 59
def prefixEnd_3736801 : Nat := 4983230072969 + 3 ^ 40 * 3736801 * 2
def baseEnd_3736801 : Nat := 1918775023201739482602271

theorem tailTrace_3736801 : CollatzResearch.WordTrace tailWord_3736801 prefixEnd_3736801 1918775023201739482602271 := by
  unfold tailWord_3736801
  simp only [CollatzResearch.WordTrace]
  refine ⟨136292329335215646646626257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90861552890143764431084171 136292329335215646646626257)
  ·
    refine ⟨102219247001411734984969693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136292329335215646646626257 102219247001411734984969693)
    ·
      refine ⟨38332217625529400619363635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102219247001411734984969693 38332217625529400619363635)
      ·
        refine ⟨57498326438294100929045453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38332217625529400619363635 57498326438294100929045453)
        ·
          refine ⟨21561872414360287848392045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57498326438294100929045453 21561872414360287848392045)
          ·
            refine ⟨8085702155385107943147017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21561872414360287848392045 8085702155385107943147017)
            ·
              refine ⟨6064276616538830957360263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8085702155385107943147017 6064276616538830957360263)
              ·
                refine ⟨9096414924808246436040395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6064276616538830957360263 9096414924808246436040395)
                ·
                  refine ⟨13644622387212369654060593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9096414924808246436040395 13644622387212369654060593)
                  ·
                    refine ⟨10233466790409277240545445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13644622387212369654060593 10233466790409277240545445)
                    ·
                      refine ⟨1918775023201739482602271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10233466790409277240545445 1918775023201739482602271)
                      ·
                        rfl

theorem cell23_3736801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 2, 1, 1, 2, 4].length) (baseStart_3736801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3736801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3736801 prefixEnd_3736801 := by exact prefixLift 3736801
  have htrace : WordTrace (prefixWord ++ tailWord_3736801) baseStart_3736801 baseEnd_3736801 := by
    simpa [prefixWord, tailWord_3736801, baseEnd_3736801] using wordTrace_append hprefix tailTrace_3736801
  have hstable : (prefixWord ++ tailWord_3736801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3736801).length < 2 ^ (prefixWord ++ tailWord_3736801).sum := by decide
  have hdescent : baseEnd_3736801 < baseStart_3736801 := by decide
  rcases family_descends (prefixWord ++ tailWord_3736801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3736805 : List Nat := [1, 3, 1, 4, 3, 1, 1, 2, 3, 2, 2]
def baseStart_3736805 : Nat := 118140960795 + 3736805 * 2 ^ 59
def prefixEnd_3736805 : Nat := 4983230072969 + 3 ^ 40 * 3736805 * 2
def baseEnd_3736805 : Nat := 1918777077124357466952253

theorem tailTrace_3736805 : CollatzResearch.WordTrace tailWord_3736805 prefixEnd_3736805 1918777077124357466952253 := by
  unfold tailWord_3736805
  simp only [CollatzResearch.WordTrace]
  refine ⟨136292475227201155329771869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90861650151467436886514579 136292475227201155329771869)
  ·
    refine ⟨51109678210200433248664451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 136292475227201155329771869 51109678210200433248664451)
    ·
      refine ⟨76664517315300649872996677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51109678210200433248664451 76664517315300649872996677)
      ·
        refine ⟨14374596996618871851186877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 76664517315300649872996677 14374596996618871851186877)
        ·
          refine ⟨5390473873732076944195079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14374596996618871851186877 5390473873732076944195079)
          ·
            refine ⟨8085710810598115416292619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5390473873732076944195079 8085710810598115416292619)
            ·
              refine ⟨12128566215897173124438929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8085710810598115416292619 12128566215897173124438929)
              ·
                refine ⟨9096424661922879843329197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12128566215897173124438929 9096424661922879843329197)
                ·
                  refine ⟨3411159248221079941248449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9096424661922879843329197 3411159248221079941248449)
                  ·
                    refine ⟨2558369436165809955936337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3411159248221079941248449 2558369436165809955936337)
                    ·
                      refine ⟨1918777077124357466952253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2558369436165809955936337 1918777077124357466952253)
                      ·
                        rfl

theorem cell23_3736805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 1, 2, 3, 2, 2].length) (baseStart_3736805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3736805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3736805 prefixEnd_3736805 := by exact prefixLift 3736805
  have htrace : WordTrace (prefixWord ++ tailWord_3736805) baseStart_3736805 baseEnd_3736805 := by
    simpa [prefixWord, tailWord_3736805, baseEnd_3736805] using wordTrace_append hprefix tailTrace_3736805
  have hstable : (prefixWord ++ tailWord_3736805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3736805).length < 2 ^ (prefixWord ++ tailWord_3736805).sum := by decide
  have hdescent : baseEnd_3736805 < baseStart_3736805 := by decide
  rcases family_descends (prefixWord ++ tailWord_3736805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3736855 : List Nat := [1, 1, 3, 4, 1, 1, 5, 1, 2, 1, 3]
def baseStart_3736855 : Nat := 118140960795 + 3736855 * 2 ^ 59
def prefixEnd_3736855 : Nat := 4983230072969 + 3 ^ 40 * 3736855 * 2
def baseEnd_3736855 : Nat := 1918802751157082271327023

theorem tailTrace_3736855 : CollatzResearch.WordTrace tailWord_3736855 prefixEnd_3736855 1918802751157082271327023 := by
  unfold tailWord_3736855
  simp only [CollatzResearch.WordTrace]
  refine ⟨136294298877020013869092019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90862865918013342579394679 136294298877020013869092019)
  ·
    refine ⟨204441448315530020803638029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136294298877020013869092019 204441448315530020803638029)
    ·
      refine ⟨76665543118323757801364261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 204441448315530020803638029 76665543118323757801364261)
      ·
        refine ⟨14374789334685704587755799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 76665543118323757801364261 14374789334685704587755799)
        ·
          refine ⟨21562184002028556881633699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14374789334685704587755799 21562184002028556881633699)
          ·
            refine ⟨32343276003042835322450549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21562184002028556881633699 32343276003042835322450549)
            ·
              refine ⟨3032182125285265811479739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 32343276003042835322450549 3032182125285265811479739)
              ·
                refine ⟨4548273187927898717219609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3032182125285265811479739 4548273187927898717219609)
                ·
                  refine ⟨3411204890945924037914707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4548273187927898717219609 3411204890945924037914707)
                  ·
                    refine ⟨5116807336418886056872061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3411204890945924037914707 5116807336418886056872061)
                    ·
                      refine ⟨1918802751157082271327023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5116807336418886056872061 1918802751157082271327023)
                      ·
                        rfl

theorem cell23_3736855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 5, 1, 2, 1, 3].length) (baseStart_3736855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3736855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3736855 prefixEnd_3736855 := by exact prefixLift 3736855
  have htrace : WordTrace (prefixWord ++ tailWord_3736855) baseStart_3736855 baseEnd_3736855 := by
    simpa [prefixWord, tailWord_3736855, baseEnd_3736855] using wordTrace_append hprefix tailTrace_3736855
  have hstable : (prefixWord ++ tailWord_3736855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3736855).length < 2 ^ (prefixWord ++ tailWord_3736855).sum := by decide
  have hdescent : baseEnd_3736855 < baseStart_3736855 := by decide
  rcases family_descends (prefixWord ++ tailWord_3736855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3736862 : List Nat := [4, 3, 2, 1, 3, 1, 2, 7]
def baseStart_3736862 : Nat := 118140960795 + 3736862 * 2 ^ 59
def prefixEnd_3736862 : Nat := 4983230072969 + 3 ^ 40 * 3736862 * 2
def baseEnd_3736862 : Nat := 71066901685987546071833

theorem tailTrace_3736862 : CollatzResearch.WordTrace tailWord_3736862 prefixEnd_3736862 71066901685987546071833 := by
  unfold tailWord_3736862
  simp only [CollatzResearch.WordTrace]
  refine ⟨17036819273499331758074605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 90863036125329769376397893 17036819273499331758074605)
  ·
    refine ⟨6388807227562249409277977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17036819273499331758074605 6388807227562249409277977)
    ·
      refine ⟨4791605420671687056958483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6388807227562249409277977 4791605420671687056958483)
      ·
        refine ⟨7187408131007530585437725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4791605420671687056958483 7187408131007530585437725)
        ·
          refine ⟨2695278049127823969539147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7187408131007530585437725 2695278049127823969539147)
          ·
            refine ⟨4042917073691735954308721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2695278049127823969539147 4042917073691735954308721)
            ·
              refine ⟨3032187805268801965731541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4042917073691735954308721 3032187805268801965731541)
              ·
                refine ⟨71066901685987546071833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3032187805268801965731541 71066901685987546071833)
                ·
                  rfl

theorem cell23_3736862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 3, 1, 2, 7].length) (baseStart_3736862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3736862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3736862 prefixEnd_3736862 := by exact prefixLift 3736862
  have htrace : WordTrace (prefixWord ++ tailWord_3736862) baseStart_3736862 baseEnd_3736862 := by
    simpa [prefixWord, tailWord_3736862, baseEnd_3736862] using wordTrace_append hprefix tailTrace_3736862
  have hstable : (prefixWord ++ tailWord_3736862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3736862).length < 2 ^ (prefixWord ++ tailWord_3736862).sum := by decide
  have hdescent : baseEnd_3736862 < baseStart_3736862 := by decide
  rcases family_descends (prefixWord ++ tailWord_3736862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3736881 : List Nat := [1, 2, 2, 3, 3, 2, 1, 1, 2, 1, 5]
def baseStart_3736881 : Nat := 118140960795 + 3736881 * 2 ^ 59
def prefixEnd_3736881 : Nat := 4983230072969 + 3 ^ 40 * 3736881 * 2
def baseEnd_3736881 : Nat := 1918816101654099169601903

theorem tailTrace_3736881 : CollatzResearch.WordTrace tailWord_3736881 prefixEnd_3736881 1918816101654099169601903 := by
  unfold tailWord_3736881
  simp only [CollatzResearch.WordTrace]
  refine ⟨136295247174925820309538497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90863498116617213539692331 136295247174925820309538497)
  ·
    refine ⟨102221435381194365232153873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136295247174925820309538497 102221435381194365232153873)
    ·
      refine ⟨76666076535895773924115405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102221435381194365232153873 76666076535895773924115405)
      ·
        refine ⟨28749778700960915221543277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76666076535895773924115405 28749778700960915221543277)
        ·
          refine ⟨10781167012860343208078729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28749778700960915221543277 10781167012860343208078729)
          ·
            refine ⟨8085875259645257406059047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10781167012860343208078729 8085875259645257406059047)
            ·
              refine ⟨12128812889467886109088571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8085875259645257406059047 12128812889467886109088571)
              ·
                refine ⟨18193219334201829163632857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12128812889467886109088571 18193219334201829163632857)
                ·
                  refine ⟨13644914500651371872724643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18193219334201829163632857 13644914500651371872724643)
                  ·
                    refine ⟨20467371750977057809086965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13644914500651371872724643 20467371750977057809086965)
                    ·
                      refine ⟨1918816101654099169601903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20467371750977057809086965 1918816101654099169601903)
                      ·
                        rfl

theorem cell23_3736881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 1, 1, 2, 1, 5].length) (baseStart_3736881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3736881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3736881 prefixEnd_3736881 := by exact prefixLift 3736881
  have htrace : WordTrace (prefixWord ++ tailWord_3736881) baseStart_3736881 baseEnd_3736881 := by
    simpa [prefixWord, tailWord_3736881, baseEnd_3736881] using wordTrace_append hprefix tailTrace_3736881
  have hstable : (prefixWord ++ tailWord_3736881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3736881).length < 2 ^ (prefixWord ++ tailWord_3736881).sum := by decide
  have hdescent : baseEnd_3736881 < baseStart_3736881 := by decide
  rcases family_descends (prefixWord ++ tailWord_3736881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3736901 : List Nat := [1, 3, 1, 1, 1, 2, 1, 8, 5]
def baseStart_3736901 : Nat := 118140960795 + 3736901 * 2 ^ 59
def prefixEnd_3736901 : Nat := 4983230072969 + 3 ^ 40 * 3736901 * 2
def baseEnd_3736901 : Nat := 213202930140798787927979

theorem tailTrace_3736901 : CollatzResearch.WordTrace tailWord_3736901 prefixEnd_3736901 213202930140798787927979 := by
  unfold tailWord_3736901
  simp only [CollatzResearch.WordTrace]
  refine ⟨136295976634853363725266557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90863984423235575816844371 136295976634853363725266557)
  ·
    refine ⟨51110991238070011396974959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 136295976634853363725266557 51110991238070011396974959)
    ·
      refine ⟨76666486857105017095462439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51110991238070011396974959 76666486857105017095462439)
      ·
        refine ⟨114999730285657525643193659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76666486857105017095462439 114999730285657525643193659)
        ·
          refine ⟨172499595428486288464790489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114999730285657525643193659 172499595428486288464790489)
          ·
            refine ⟨129374696571364716348592867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 172499595428486288464790489 129374696571364716348592867)
            ·
              refine ⟨194062044857047074522889301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 129374696571364716348592867 194062044857047074522889301)
              ·
                refine ⟨2274164588168520404565109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 194062044857047074522889301 2274164588168520404565109)
                ·
                  refine ⟨213202930140798787927979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2274164588168520404565109 213202930140798787927979)
                  ·
                    rfl

theorem cell23_3736901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 8, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 8, 5].length) (baseStart_3736901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3736901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3736901 prefixEnd_3736901 := by exact prefixLift 3736901
  have htrace : WordTrace (prefixWord ++ tailWord_3736901) baseStart_3736901 baseEnd_3736901 := by
    simpa [prefixWord, tailWord_3736901, baseEnd_3736901] using wordTrace_append hprefix tailTrace_3736901
  have hstable : (prefixWord ++ tailWord_3736901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3736901).length < 2 ^ (prefixWord ++ tailWord_3736901).sum := by decide
  have hdescent : baseEnd_3736901 < baseStart_3736901 := by decide
  rcases family_descends (prefixWord ++ tailWord_3736901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3736931 : List Nat := [1, 1, 1, 5, 2, 2, 1, 3, 2, 5]
def baseStart_3736931 : Nat := 118140960795 + 3736931 * 2 ^ 59
def prefixEnd_3736931 : Nat := 4983230072969 + 3 ^ 40 * 3736931 * 2
def baseEnd_3736931 : Nat := 639613925228941324658891

theorem tailTrace_3736931 : CollatzResearch.WordTrace tailWord_3736931 prefixEnd_3736931 639613925228941324658891 := by
  unfold tailWord_3736931
  simp only [CollatzResearch.WordTrace]
  refine ⟨136297070824744678848858647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90864713883163119232572431 136297070824744678848858647)
  ·
    refine ⟨204445606237117018273287971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136297070824744678848858647 204445606237117018273287971)
    ·
      refine ⟨306668409355675527409931957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204445606237117018273287971 306668409355675527409931957)
      ·
        refine ⟨28750163377094580694681121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 306668409355675527409931957 28750163377094580694681121)
        ·
          refine ⟨21562622532820935521010841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28750163377094580694681121 21562622532820935521010841)
          ·
            refine ⟨16171966899615701640758131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21562622532820935521010841 16171966899615701640758131)
            ·
              refine ⟨24257950349423552461137197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16171966899615701640758131 24257950349423552461137197)
              ·
                refine ⟨9096731381033832172926449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24257950349423552461137197 9096731381033832172926449)
                ·
                  refine ⟨6822548535775374129694837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9096731381033832172926449 6822548535775374129694837)
                  ·
                    refine ⟨639613925228941324658891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6822548535775374129694837 639613925228941324658891)
                    ·
                      rfl

theorem cell23_3736931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 1, 3, 2, 5].length) (baseStart_3736931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3736931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3736931 prefixEnd_3736931 := by exact prefixLift 3736931
  have htrace : WordTrace (prefixWord ++ tailWord_3736931) baseStart_3736931 baseEnd_3736931 := by
    simpa [prefixWord, tailWord_3736931, baseEnd_3736931] using wordTrace_append hprefix tailTrace_3736931
  have hstable : (prefixWord ++ tailWord_3736931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3736931).length < 2 ^ (prefixWord ++ tailWord_3736931).sum := by decide
  have hdescent : baseEnd_3736931 < baseStart_3736931 := by decide
  rcases family_descends (prefixWord ++ tailWord_3736931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3736941 : List Nat := [1, 5, 1, 1, 1, 3, 1, 2, 1, 2, 5]
def baseStart_3736941 : Nat := 118140960795 + 3736941 * 2 ^ 59
def prefixEnd_3736941 : Nat := 4983230072969 + 3 ^ 40 * 3736941 * 2
def baseEnd_3736941 : Nat := 1918846910493368934851627

theorem tailTrace_3736941 : CollatzResearch.WordTrace tailWord_3736941 prefixEnd_3736941 1918846910493368934851627 := by
  unfold tailWord_3736941
  simp only [CollatzResearch.WordTrace]
  refine ⟨136297435554708450556722677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90864957036472300371148451 136297435554708450556722677)
  ·
    refine ⟨12777884583253917239692751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 136297435554708450556722677 12777884583253917239692751)
    ·
      refine ⟨19166826874880875859539127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12777884583253917239692751 19166826874880875859539127)
      ·
        refine ⟨28750240312321313789308691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19166826874880875859539127 28750240312321313789308691)
        ·
          refine ⟨43125360468481970683963037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28750240312321313789308691 43125360468481970683963037)
          ·
            refine ⟨16172010175680739006486139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43125360468481970683963037 16172010175680739006486139)
            ·
              refine ⟨24258015263521108509729209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16172010175680739006486139 24258015263521108509729209)
              ·
                refine ⟨18193511447640831382296907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24258015263521108509729209 18193511447640831382296907)
                ·
                  refine ⟨27290267171461247073445361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18193511447640831382296907 27290267171461247073445361)
                  ·
                    refine ⟨20467700378595935305084021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27290267171461247073445361 20467700378595935305084021)
                    ·
                      refine ⟨1918846910493368934851627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20467700378595935305084021 1918846910493368934851627)
                      ·
                        rfl

theorem cell23_3736941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 1, 2, 1, 2, 5].length) (baseStart_3736941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3736941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3736941 prefixEnd_3736941 := by exact prefixLift 3736941
  have htrace : WordTrace (prefixWord ++ tailWord_3736941) baseStart_3736941 baseEnd_3736941 := by
    simpa [prefixWord, tailWord_3736941, baseEnd_3736941] using wordTrace_append hprefix tailTrace_3736941
  have hstable : (prefixWord ++ tailWord_3736941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3736941).length < 2 ^ (prefixWord ++ tailWord_3736941).sum := by decide
  have hdescent : baseEnd_3736941 < baseStart_3736941 := by decide
  rcases family_descends (prefixWord ++ tailWord_3736941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3736951 : List Nat := [1, 1, 3, 1, 1, 2, 3, 4, 2, 1, 4]
def baseStart_3736951 : Nat := 118140960795 + 3736951 * 2 ^ 59
def prefixEnd_3736951 : Nat := 4983230072969 + 3 ^ 40 * 3736951 * 2
def baseEnd_3736951 : Nat := 1918852045299913895726581

theorem tailTrace_3736951 : CollatzResearch.WordTrace tailWord_3736951 prefixEnd_3736951 1918852045299913895726581 := by
  unfold tailWord_3736951
  simp only [CollatzResearch.WordTrace]
  refine ⟨136297800284672222264586707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90865200189781481509724471 136297800284672222264586707)
  ·
    refine ⟨204446700427008333396880061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136297800284672222264586707 204446700427008333396880061)
    ·
      refine ⟨76667512660128125023830023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 204446700427008333396880061 76667512660128125023830023)
      ·
        refine ⟨115001268990192187535745035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76667512660128125023830023 115001268990192187535745035)
        ·
          refine ⟨172501903485288281303617553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115001268990192187535745035 172501903485288281303617553)
          ·
            refine ⟨129376427613966210977713165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 172501903485288281303617553 129376427613966210977713165)
            ·
              refine ⟨48516160355237329116642437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 129376427613966210977713165 48516160355237329116642437)
              ·
                refine ⟨9096780066606999209370457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48516160355237329116642437 9096780066606999209370457)
                ·
                  refine ⟨6822585049955249407027843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9096780066606999209370457 6822585049955249407027843)
                  ·
                    refine ⟨10233877574932874110541765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6822585049955249407027843 10233877574932874110541765)
                    ·
                      refine ⟨1918852045299913895726581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10233877574932874110541765 1918852045299913895726581)
                      ·
                        rfl

theorem cell23_3736951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 4, 2, 1, 4].length) (baseStart_3736951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3736951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3736951 prefixEnd_3736951 := by exact prefixLift 3736951
  have htrace : WordTrace (prefixWord ++ tailWord_3736951) baseStart_3736951 baseEnd_3736951 := by
    simpa [prefixWord, tailWord_3736951, baseEnd_3736951] using wordTrace_append hprefix tailTrace_3736951
  have hstable : (prefixWord ++ tailWord_3736951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3736951).length < 2 ^ (prefixWord ++ tailWord_3736951).sum := by decide
  have hdescent : baseEnd_3736951 < baseStart_3736951 := by decide
  rcases family_descends (prefixWord ++ tailWord_3736951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3736968 : List Nat := [2, 1, 3, 3, 1, 2, 1, 1, 1, 6, 2]
def baseStart_3736968 : Nat := 118140960795 + 3736968 * 2 ^ 59
def prefixEnd_3736968 : Nat := 4983230072969 + 3 ^ 40 * 3736968 * 2
def baseEnd_3736968 : Nat := 1918860774471040329214003

theorem tailTrace_3736968 : CollatzResearch.WordTrace tailWord_3736968 prefixEnd_3736968 1918860774471040329214003 := by
  unfold tailWord_3736968
  simp only [CollatzResearch.WordTrace]
  refine ⟨68149210162805317083977779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90865613550407089445303705 68149210162805317083977779)
  ·
    refine ⟨102223815244207975625966669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68149210162805317083977779 102223815244207975625966669)
    ·
      refine ⟨38333930716577990859737501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102223815244207975625966669 38333930716577990859737501)
      ·
        refine ⟨14375224018716746572401563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38333930716577990859737501 14375224018716746572401563)
        ·
          refine ⟨21562836028075119858602345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14375224018716746572401563 21562836028075119858602345)
          ·
            refine ⟨16172127021056339893951759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21562836028075119858602345 16172127021056339893951759)
            ·
              refine ⟨24258190531584509840927639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16172127021056339893951759 24258190531584509840927639)
              ·
                refine ⟨36387285797376764761391459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24258190531584509840927639 36387285797376764761391459)
                ·
                  refine ⟨54580928696065147142087189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36387285797376764761391459 54580928696065147142087189)
                  ·
                    refine ⟨2558481032628053772285337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 54580928696065147142087189 2558481032628053772285337)
                    ·
                      refine ⟨1918860774471040329214003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2558481032628053772285337 1918860774471040329214003)
                      ·
                        rfl

theorem cell23_3736968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 1, 1, 1, 6, 2].length) (baseStart_3736968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3736968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3736968 prefixEnd_3736968 := by exact prefixLift 3736968
  have htrace : WordTrace (prefixWord ++ tailWord_3736968) baseStart_3736968 baseEnd_3736968 := by
    simpa [prefixWord, tailWord_3736968, baseEnd_3736968] using wordTrace_append hprefix tailTrace_3736968
  have hstable : (prefixWord ++ tailWord_3736968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3736968).length < 2 ^ (prefixWord ++ tailWord_3736968).sum := by decide
  have hdescent : baseEnd_3736968 < baseStart_3736968 := by decide
  rcases family_descends (prefixWord ++ tailWord_3736968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3736971 : List Nat := [1, 1, 1, 1, 4, 3, 2, 2, 1, 4, 3]
def baseStart_3736971 : Nat := 118140960795 + 3736971 * 2 ^ 59
def prefixEnd_3736971 : Nat := 4983230072969 + 3 ^ 40 * 3736971 * 2
def baseEnd_3736971 : Nat := 1918862314913003817476489

theorem tailTrace_3736971 : CollatzResearch.WordTrace tailWord_3736971 prefixEnd_3736971 1918862314913003817476489 := by
  unfold tailWord_3736971
  simp only [CollatzResearch.WordTrace]
  refine ⟨136298529744599765680314767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90865686496399843786876511 136298529744599765680314767)
  ·
    refine ⟨204447794616899648520472151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136298529744599765680314767 204447794616899648520472151)
    ·
      refine ⟨306671691925349472780708227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204447794616899648520472151 306671691925349472780708227)
      ·
        refine ⟨460007537888024209171062341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 306671691925349472780708227 460007537888024209171062341)
        ·
          refine ⟨86251413354004539219574189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 460007537888024209171062341 86251413354004539219574189)
          ·
            refine ⟨32344280007751702207340321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 86251413354004539219574189 32344280007751702207340321)
            ·
              refine ⟨24258210005813776655505241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32344280007751702207340321 24258210005813776655505241)
              ·
                refine ⟨18193657504360332491628931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24258210005813776655505241 18193657504360332491628931)
                ·
                  refine ⟨27290486256540498737443397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18193657504360332491628931 27290486256540498737443397)
                  ·
                    refine ⟨5116966173101343513270637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27290486256540498737443397 5116966173101343513270637)
                    ·
                      refine ⟨1918862314913003817476489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5116966173101343513270637 1918862314913003817476489)
                      ·
                        rfl

theorem cell23_3736971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 2, 2, 1, 4, 3].length) (baseStart_3736971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3736971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3736971 prefixEnd_3736971 := by exact prefixLift 3736971
  have htrace : WordTrace (prefixWord ++ tailWord_3736971) baseStart_3736971 baseEnd_3736971 := by
    simpa [prefixWord, tailWord_3736971, baseEnd_3736971] using wordTrace_append hprefix tailTrace_3736971
  have hstable : (prefixWord ++ tailWord_3736971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3736971).length < 2 ^ (prefixWord ++ tailWord_3736971).sum := by decide
  have hdescent : baseEnd_3736971 < baseStart_3736971 := by decide
  rcases family_descends (prefixWord ++ tailWord_3736971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3736995 : List Nat := [1, 1, 1, 4, 1, 3, 4, 3, 1, 4]
def baseStart_3736995 : Nat := 118140960795 + 3736995 * 2 ^ 59
def prefixEnd_3736995 : Nat := 4983230072969 + 3 ^ 40 * 3736995 * 2
def baseEnd_3736995 : Nat := 639624879482903907858793

theorem tailTrace_3736995 : CollatzResearch.WordTrace tailWord_3736995 prefixEnd_3736995 639624879482903907858793 := by
  unfold tailWord_3736995
  simp only [CollatzResearch.WordTrace]
  refine ⟨136299405096512817779188439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90866270064341878519458959 136299405096512817779188439)
  ·
    refine ⟨204449107644769226668782659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136299405096512817779188439 204449107644769226668782659)
    ·
      refine ⟨306673661467153840003173989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204449107644769226668782659 306673661467153840003173989)
      ·
        refine ⟨57501311525091345000595123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 306673661467153840003173989 57501311525091345000595123)
        ·
          refine ⟨86251967287637017500892685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57501311525091345000595123 86251967287637017500892685)
          ·
            refine ⟨32344487732863881562834757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 86251967287637017500892685 32344487732863881562834757)
            ·
              refine ⟨6064591449911977793031517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32344487732863881562834757 6064591449911977793031517)
              ·
                refine ⟨2274221793716991672386819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6064591449911977793031517 2274221793716991672386819)
                ·
                  refine ⟨3411332690575487508580229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2274221793716991672386819 3411332690575487508580229)
                  ·
                    refine ⟨639624879482903907858793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3411332690575487508580229 639624879482903907858793)
                    ·
                      rfl

theorem cell23_3736995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 4, 3, 1, 4].length) (baseStart_3736995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3736995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3736995 prefixEnd_3736995 := by exact prefixLift 3736995
  have htrace : WordTrace (prefixWord ++ tailWord_3736995) baseStart_3736995 baseEnd_3736995 := by
    simpa [prefixWord, tailWord_3736995, baseEnd_3736995] using wordTrace_append hprefix tailTrace_3736995
  have hstable : (prefixWord ++ tailWord_3736995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3736995).length < 2 ^ (prefixWord ++ tailWord_3736995).sum := by decide
  have hdescent : baseEnd_3736995 < baseStart_3736995 := by decide
  rcases family_descends (prefixWord ++ tailWord_3736995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3737038 : List Nat := [4, 1, 1, 1, 2, 1, 3, 4, 1, 5]
def baseStart_3737038 : Nat := 118140960795 + 3737038 * 2 ^ 59
def prefixEnd_3737038 : Nat := 4983230072969 + 3 ^ 40 * 3737038 * 2
def baseEnd_3737038 : Nat := 639632239372285018446227

theorem tailTrace_3737038 : CollatzResearch.WordTrace tailWord_3737038 prefixEnd_3737038 639632239372285018446227 := by
  unfold tailWord_3737038
  simp only [CollatzResearch.WordTrace]
  refine ⟨17037621679419629515375471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 90867315623571357415335845 17037621679419629515375471)
  ·
    refine ⟨25556432519129444273063207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17037621679419629515375471 25556432519129444273063207)
    ·
      refine ⟨38334648778694166409594811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25556432519129444273063207 38334648778694166409594811)
      ·
        refine ⟨57501973168041249614392217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38334648778694166409594811 57501973168041249614392217)
        ·
          refine ⟨43126479876030937210794163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57501973168041249614392217 43126479876030937210794163)
          ·
            refine ⟨64689719814046405816191245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43126479876030937210794163 64689719814046405816191245)
            ·
              refine ⟨24258644930267402181071717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64689719814046405816191245 24258644930267402181071717)
              ·
                refine ⟨4548495924425137908950947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24258644930267402181071717 4548495924425137908950947)
                ·
                  refine ⟨6822743886637706863426421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4548495924425137908950947 6822743886637706863426421)
                  ·
                    refine ⟨639632239372285018446227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6822743886637706863426421 639632239372285018446227)
                    ·
                      rfl

theorem cell23_3737038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 3, 4, 1, 5].length) (baseStart_3737038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3737038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3737038 prefixEnd_3737038 := by exact prefixLift 3737038
  have htrace : WordTrace (prefixWord ++ tailWord_3737038) baseStart_3737038 baseEnd_3737038 := by
    simpa [prefixWord, tailWord_3737038, baseEnd_3737038] using wordTrace_append hprefix tailTrace_3737038
  have hstable : (prefixWord ++ tailWord_3737038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3737038).length < 2 ^ (prefixWord ++ tailWord_3737038).sum := by decide
  have hdescent : baseEnd_3737038 < baseStart_3737038 := by decide
  rcases family_descends (prefixWord ++ tailWord_3737038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3737045 : List Nat := [1, 3, 2, 3, 1, 1, 2, 3, 2, 3, 2]
def baseStart_3737045 : Nat := 118140960795 + 3737045 * 2 ^ 59
def prefixEnd_3737045 : Nat := 4983230072969 + 3 ^ 40 * 3737045 * 2
def baseEnd_3737045 : Nat := 1918900312481436527951149

theorem tailTrace_3737045 : CollatzResearch.WordTrace tailWord_3737045 prefixEnd_3737045 1918900312481436527951149 := by
  unfold tailWord_3737045
  simp only [CollatzResearch.WordTrace]
  refine ⟨136301228746331676318508589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90867485830887784212339059 136301228746331676318508589)
  ·
    refine ⟨51112960779874378619440721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 136301228746331676318508589 51112960779874378619440721)
    ·
      refine ⟨38334720584905783964580541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51112960779874378619440721 38334720584905783964580541)
      ·
        refine ⟨14375520219339668986717703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38334720584905783964580541 14375520219339668986717703)
        ·
          refine ⟨21563280329009503480076555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14375520219339668986717703 21563280329009503480076555)
          ·
            refine ⟨32344920493514255220114833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21563280329009503480076555 32344920493514255220114833)
            ·
              refine ⟨24258690370135691415086125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32344920493514255220114833 24258690370135691415086125)
              ·
                refine ⟨9097008888800884280657297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24258690370135691415086125 9097008888800884280657297)
                ·
                  refine ⟨6822756666600663210492973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9097008888800884280657297 6822756666600663210492973)
                  ·
                    refine ⟨2558533749975248703934865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6822756666600663210492973 2558533749975248703934865)
                    ·
                      refine ⟨1918900312481436527951149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2558533749975248703934865 1918900312481436527951149)
                      ·
                        rfl

theorem cell23_3737045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 2, 3, 2, 3, 2].length) (baseStart_3737045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3737045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3737045 prefixEnd_3737045 := by exact prefixLift 3737045
  have htrace : WordTrace (prefixWord ++ tailWord_3737045) baseStart_3737045 baseEnd_3737045 := by
    simpa [prefixWord, tailWord_3737045, baseEnd_3737045] using wordTrace_append hprefix tailTrace_3737045
  have hstable : (prefixWord ++ tailWord_3737045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3737045).length < 2 ^ (prefixWord ++ tailWord_3737045).sum := by decide
  have hdescent : baseEnd_3737045 < baseStart_3737045 := by decide
  rcases family_descends (prefixWord ++ tailWord_3737045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3737069 : List Nat := [1, 5, 1, 3, 2, 2, 1, 1, 3, 1, 3]
def baseStart_3737069 : Nat := 118140960795 + 3737069 * 2 ^ 59
def prefixEnd_3737069 : Nat := 4983230072969 + 3 ^ 40 * 3737069 * 2
def baseEnd_3737069 : Nat := 1918912636017144434051039

theorem tailTrace_3737069 : CollatzResearch.WordTrace tailWord_3737069 prefixEnd_3737069 1918912636017144434051039 := by
  unfold tailWord_3737069
  simp only [CollatzResearch.WordTrace]
  refine ⟨136302104098244728417382261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90868069398829818944921507 136302104098244728417382261)
  ·
    refine ⟨12778322259210443289129587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 136302104098244728417382261 12778322259210443289129587)
    ·
      refine ⟨19167483388815664933694381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12778322259210443289129587 19167483388815664933694381)
      ·
        refine ⟨7187806270805874350135393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19167483388815664933694381 7187806270805874350135393)
        ·
          refine ⟨5390854703104405762601545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7187806270805874350135393 5390854703104405762601545)
          ·
            refine ⟨4043141027328304321951159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5390854703104405762601545 4043141027328304321951159)
            ·
              refine ⟨6064711540992456482926739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4043141027328304321951159 6064711540992456482926739)
              ·
                refine ⟨9097067311488684724390109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6064711540992456482926739 9097067311488684724390109)
                ·
                  refine ⟨3411400241808256771646291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9097067311488684724390109 3411400241808256771646291)
                  ·
                    refine ⟨5117100362712385157469437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3411400241808256771646291 5117100362712385157469437)
                    ·
                      refine ⟨1918912636017144434051039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5117100362712385157469437 1918912636017144434051039)
                      ·
                        rfl

theorem cell23_3737069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 2, 1, 1, 3, 1, 3].length) (baseStart_3737069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3737069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3737069 prefixEnd_3737069 := by exact prefixLift 3737069
  have htrace : WordTrace (prefixWord ++ tailWord_3737069) baseStart_3737069 baseEnd_3737069 := by
    simpa [prefixWord, tailWord_3737069, baseEnd_3737069] using wordTrace_append hprefix tailTrace_3737069
  have hstable : (prefixWord ++ tailWord_3737069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3737069).length < 2 ^ (prefixWord ++ tailWord_3737069).sum := by decide
  have hdescent : baseEnd_3737069 < baseStart_3737069 := by decide
  rcases family_descends (prefixWord ++ tailWord_3737069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3737071 : List Nat := [1, 1, 2, 1, 4, 1, 3, 2, 1, 1, 6]
def baseStart_3737071 : Nat := 118140960795 + 3737071 * 2 ^ 59
def prefixEnd_3737071 : Nat := 4983230072969 + 3 ^ 40 * 3737071 * 2
def baseEnd_3737071 : Nat := 1918913662978453426226029

theorem tailTrace_3737071 : CollatzResearch.WordTrace tailWord_3737071 prefixEnd_3737071 1918913662978453426226029 := by
  unfold tailWord_3737071
  simp only [CollatzResearch.WordTrace]
  refine ⟨136302177044237482758955067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90868118029491655172636711 136302177044237482758955067)
  ·
    refine ⟨204453265566356224138432601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136302177044237482758955067 204453265566356224138432601)
    ·
      refine ⟨153339949174767168103824451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 204453265566356224138432601 153339949174767168103824451)
      ·
        refine ⟨230009923762150752155736677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153339949174767168103824451 230009923762150752155736677)
        ·
          refine ⟨43126860705403266029200627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 230009923762150752155736677 43126860705403266029200627)
          ·
            refine ⟨64690291058104899043800941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43126860705403266029200627 64690291058104899043800941)
            ·
              refine ⟨24258859146789337141425353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64690291058104899043800941 24258859146789337141425353)
              ·
                refine ⟨18194144360092002856069015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24258859146789337141425353 18194144360092002856069015)
                ·
                  refine ⟨27291216540138004284103523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18194144360092002856069015 27291216540138004284103523)
                  ·
                    refine ⟨40936824810207006426155285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27291216540138004284103523 40936824810207006426155285)
                    ·
                      refine ⟨1918913662978453426226029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 40936824810207006426155285 1918913662978453426226029)
                      ·
                        rfl

theorem cell23_3737071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 3, 2, 1, 1, 6].length) (baseStart_3737071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3737071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3737071 prefixEnd_3737071 := by exact prefixLift 3737071
  have htrace : WordTrace (prefixWord ++ tailWord_3737071) baseStart_3737071 baseEnd_3737071 := by
    simpa [prefixWord, tailWord_3737071, baseEnd_3737071] using wordTrace_append hprefix tailTrace_3737071
  have hstable : (prefixWord ++ tailWord_3737071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3737071).length < 2 ^ (prefixWord ++ tailWord_3737071).sum := by decide
  have hdescent : baseEnd_3737071 < baseStart_3737071 := by decide
  rcases family_descends (prefixWord ++ tailWord_3737071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3737075 : List Nat := [1, 1, 1, 2, 2, 2, 2, 5, 3, 2, 2]
def baseStart_3737075 : Nat := 118140960795 + 3737075 * 2 ^ 59
def prefixEnd_3737075 : Nat := 4983230072969 + 3 ^ 40 * 3737075 * 2
def baseEnd_3737075 : Nat := 1918915716901071410576011

theorem tailTrace_3737075 : CollatzResearch.WordTrace tailWord_3737075 prefixEnd_3737075 1918915716901071410576011 := by
  unfold tailWord_3737075
  simp only [CollatzResearch.WordTrace]
  refine ⟨136302322936222991442100679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90868215290815327628067119 136302322936222991442100679)
  ·
    refine ⟨204453484404334487163151019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136302322936222991442100679 204453484404334487163151019)
    ·
      refine ⟨306680226606501730744726529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204453484404334487163151019 306680226606501730744726529)
      ·
        refine ⟨230010169954876298058544897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 306680226606501730744726529 230010169954876298058544897)
        ·
          refine ⟨172507627466157223543908673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 230010169954876298058544897 172507627466157223543908673)
          ·
            refine ⟨129380720599617917657931505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 172507627466157223543908673 129380720599617917657931505)
            ·
              refine ⟨97035540449713438243448629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 129380720599617917657931505 97035540449713438243448629)
              ·
                refine ⟨9097081917160634835323309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 97035540449713438243448629 9097081917160634835323309)
                ·
                  refine ⟨3411405718935238063246241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9097081917160634835323309 3411405718935238063246241)
                  ·
                    refine ⟨2558554289201428547434681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3411405718935238063246241 2558554289201428547434681)
                    ·
                      refine ⟨1918915716901071410576011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2558554289201428547434681 1918915716901071410576011)
                      ·
                        rfl

theorem cell23_3737075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 5, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 5, 3, 2, 2].length) (baseStart_3737075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3737075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3737075 prefixEnd_3737075 := by exact prefixLift 3737075
  have htrace : WordTrace (prefixWord ++ tailWord_3737075) baseStart_3737075 baseEnd_3737075 := by
    simpa [prefixWord, tailWord_3737075, baseEnd_3737075] using wordTrace_append hprefix tailTrace_3737075
  have hstable : (prefixWord ++ tailWord_3737075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3737075).length < 2 ^ (prefixWord ++ tailWord_3737075).sum := by decide
  have hdescent : baseEnd_3737075 < baseStart_3737075 := by decide
  rcases family_descends (prefixWord ++ tailWord_3737075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3737085 : List Nat := [1, 4, 1, 1, 1, 5, 1, 3, 2, 4]
def baseStart_3737085 : Nat := 118140960795 + 3737085 * 2 ^ 59
def prefixEnd_3737085 : Nat := 4983230072969 + 3 ^ 40 * 3737085 * 2
def baseEnd_3737085 : Nat := 639640283902538790483655

theorem tailTrace_3737085 : CollatzResearch.WordTrace tailWord_3737085 prefixEnd_3737085 639640283902538790483655 := by
  unfold tailWord_3737085
  simp only [CollatzResearch.WordTrace]
  refine ⟨136302687666186763149964709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90868458444124508766643139 136302687666186763149964709)
  ·
    refine ⟨25556753937410018090618383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 136302687666186763149964709 25556753937410018090618383)
    ·
      refine ⟨38335130906115027135927575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25556753937410018090618383 38335130906115027135927575)
      ·
        refine ⟨57502696359172540703891363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38335130906115027135927575 57502696359172540703891363)
        ·
          refine ⟨86254044538758811055837045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57502696359172540703891363 86254044538758811055837045)
          ·
            refine ⟨8086316675508638536484723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 86254044538758811055837045 8086316675508638536484723)
            ·
              refine ⟨12129475013262957804727085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8086316675508638536484723 12129475013262957804727085)
              ·
                refine ⟨4548553129973609176772657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12129475013262957804727085 4548553129973609176772657)
                ·
                  refine ⟨3411414847480206882579493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4548553129973609176772657 3411414847480206882579493)
                  ·
                    refine ⟨639640283902538790483655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3411414847480206882579493 639640283902538790483655)
                    ·
                      rfl

theorem cell23_3737085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 1, 3, 2, 4].length) (baseStart_3737085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3737085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3737085 prefixEnd_3737085 := by exact prefixLift 3737085
  have htrace : WordTrace (prefixWord ++ tailWord_3737085) baseStart_3737085 baseEnd_3737085 := by
    simpa [prefixWord, tailWord_3737085, baseEnd_3737085] using wordTrace_append hprefix tailTrace_3737085
  have hstable : (prefixWord ++ tailWord_3737085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3737085).length < 2 ^ (prefixWord ++ tailWord_3737085).sum := by decide
  have hdescent : baseEnd_3737085 < baseStart_3737085 := by decide
  rcases family_descends (prefixWord ++ tailWord_3737085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3737095 : List Nat := [1, 1, 4, 3, 2, 2, 1, 1, 3, 2, 3]
def baseStart_3737095 : Nat := 118140960795 + 3737095 * 2 ^ 59
def prefixEnd_3737095 : Nat := 4983230072969 + 3 ^ 40 * 3737095 * 2
def baseEnd_3737095 : Nat := 1918925986514161332325919

theorem tailTrace_3737095 : CollatzResearch.WordTrace tailWord_3737095 prefixEnd_3737095 1918925986514161332325919 := by
  unfold tailWord_3737095
  simp only [CollatzResearch.WordTrace]
  refine ⟨136303052396150534857828739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90868701597433689905219159 136303052396150534857828739)
  ·
    refine ⟨204454578594225802286743109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136303052396150534857828739 204454578594225802286743109)
    ·
      refine ⟨38335233486417337928764333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 204454578594225802286743109 38335233486417337928764333)
      ·
        refine ⟨14375712557406501723286625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38335233486417337928764333 14375712557406501723286625)
        ·
          refine ⟨10781784418054876292464969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14375712557406501723286625 10781784418054876292464969)
          ·
            refine ⟨8086338313541157219348727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10781784418054876292464969 8086338313541157219348727)
            ·
              refine ⟨12129507470311735829023091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8086338313541157219348727 12129507470311735829023091)
              ·
                refine ⟨18194261205467603743534637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12129507470311735829023091 18194261205467603743534637)
                ·
                  refine ⟨6822847952050351403825489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18194261205467603743534637 6822847952050351403825489)
                  ·
                    refine ⟨5117135964037763552869117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6822847952050351403825489 5117135964037763552869117)
                    ·
                      refine ⟨1918925986514161332325919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5117135964037763552869117 1918925986514161332325919)
                      ·
                        rfl

theorem cell23_3737095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 1, 1, 3, 2, 3].length) (baseStart_3737095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3737095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3737095 prefixEnd_3737095 := by exact prefixLift 3737095
  have htrace : WordTrace (prefixWord ++ tailWord_3737095) baseStart_3737095 baseEnd_3737095 := by
    simpa [prefixWord, tailWord_3737095, baseEnd_3737095] using wordTrace_append hprefix tailTrace_3737095
  have hstable : (prefixWord ++ tailWord_3737095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3737095).length < 2 ^ (prefixWord ++ tailWord_3737095).sum := by decide
  have hdescent : baseEnd_3737095 < baseStart_3737095 := by decide
  rcases family_descends (prefixWord ++ tailWord_3737095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3737112 : List Nat := [2, 1, 2, 3, 5, 1, 1, 1, 1, 1, 5]
def baseStart_3737112 : Nat := 118140960795 + 3737112 * 2 ^ 59
def prefixEnd_3737112 : Nat := 4983230072969 + 3 ^ 40 * 3737112 * 2
def baseEnd_3737112 : Nat := 1918934715685287765813341

theorem tailTrace_3737112 : CollatzResearch.WordTrace tailWord_3737112 prefixEnd_3737112 1918934715685287765813341 := by
  unfold tailWord_3737112
  simp only [CollatzResearch.WordTrace]
  refine ⟨68151836218544473380598795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90869114958059297840798393 68151836218544473380598795)
  ·
    refine ⟨102227754327816710070898193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68151836218544473380598795 102227754327816710070898193)
    ·
      refine ⟨76670815745862532553173645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102227754327816710070898193 76670815745862532553173645)
      ·
        refine ⟨28751555904698449707440117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76670815745862532553173645 28751555904698449707440117)
        ·
          refine ⟨2695458366065479660072511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 28751555904698449707440117 2695458366065479660072511)
          ·
            refine ⟨4043187549098219490108767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2695458366065479660072511 4043187549098219490108767)
            ·
              refine ⟨6064781323647329235163151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4043187549098219490108767 6064781323647329235163151)
              ·
                refine ⟨9097171985470993852744727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6064781323647329235163151 9097171985470993852744727)
                ·
                  refine ⟨13645757978206490779117091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9097171985470993852744727 13645757978206490779117091)
                  ·
                    refine ⟨20468636967309736168675637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13645757978206490779117091 20468636967309736168675637)
                    ·
                      refine ⟨1918934715685287765813341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20468636967309736168675637 1918934715685287765813341)
                      ·
                        rfl

theorem cell23_3737112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 5, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 5, 1, 1, 1, 1, 1, 5].length) (baseStart_3737112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3737112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3737112 prefixEnd_3737112 := by exact prefixLift 3737112
  have htrace : WordTrace (prefixWord ++ tailWord_3737112) baseStart_3737112 baseEnd_3737112 := by
    simpa [prefixWord, tailWord_3737112, baseEnd_3737112] using wordTrace_append hprefix tailTrace_3737112
  have hstable : (prefixWord ++ tailWord_3737112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3737112).length < 2 ^ (prefixWord ++ tailWord_3737112).sum := by decide
  have hdescent : baseEnd_3737112 < baseStart_3737112 := by decide
  rcases family_descends (prefixWord ++ tailWord_3737112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3737188 : List Nat := [2, 3, 1, 1, 2, 3, 1, 3, 7]
def baseStart_3737188 : Nat := 118140960795 + 3737188 * 2 ^ 59
def prefixEnd_3737188 : Nat := 4983230072969 + 3 ^ 40 * 3737188 * 2
def baseEnd_3737188 : Nat := 213219304468336607606999

theorem tailTrace_3737188 : CollatzResearch.WordTrace tailWord_3737188 prefixEnd_3737188 213219304468336607606999 := by
  unfold tailWord_3737188
  simp only [CollatzResearch.WordTrace]
  refine ⟨68153222192406805870482109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90870962923209074493976145 68153222192406805870482109)
  ·
    refine ⟨25557458322152552201430791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68153222192406805870482109 25557458322152552201430791)
    ·
      refine ⟨38336187483228828302146187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25557458322152552201430791 38336187483228828302146187)
      ·
        refine ⟨57504281224843242453219281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38336187483228828302146187 57504281224843242453219281)
        ·
          refine ⟨43128210918632431839914461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57504281224843242453219281 43128210918632431839914461)
          ·
            refine ⟨16173079094487161939967923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43128210918632431839914461 16173079094487161939967923)
            ·
              refine ⟨24259618641730742909951885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16173079094487161939967923 24259618641730742909951885)
              ·
                refine ⟨9097356990649028591231957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24259618641730742909951885 9097356990649028591231957)
                ·
                  refine ⟨213219304468336607606999, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9097356990649028591231957 213219304468336607606999)
                  ·
                    rfl

theorem cell23_3737188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 1, 3, 7].length) (baseStart_3737188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3737188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3737188 prefixEnd_3737188 := by exact prefixLift 3737188
  have htrace : WordTrace (prefixWord ++ tailWord_3737188) baseStart_3737188 baseEnd_3737188 := by
    simpa [prefixWord, tailWord_3737188, baseEnd_3737188] using wordTrace_append hprefix tailTrace_3737188
  have hstable : (prefixWord ++ tailWord_3737188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3737188).length < 2 ^ (prefixWord ++ tailWord_3737188).sum := by decide
  have hdescent : baseEnd_3737188 < baseStart_3737188 := by decide
  rcases family_descends (prefixWord ++ tailWord_3737188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3737205 : List Nat := [1, 3, 4, 2, 1, 1, 2, 2, 7]
def baseStart_3737205 : Nat := 118140960795 + 3737205 * 2 ^ 59
def prefixEnd_3737205 : Nat := 4983230072969 + 3 ^ 40 * 3737205 * 2
def baseEnd_3737205 : Nat := 213220274376239544661157

theorem tailTrace_3737205 : CollatzResearch.WordTrace tailWord_3737205 prefixEnd_3737205 213220274376239544661157 := by
  unfold tailWord_3737205
  simp only [CollatzResearch.WordTrace]
  refine ⟨136307064425752023644333069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90871376283834682429555379 136307064425752023644333069)
  ·
    refine ⟨51115149159657008866624901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 136307064425752023644333069 51115149159657008866624901)
    ·
      refine ⟨9584090467435689162492169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 51115149159657008866624901 9584090467435689162492169)
      ·
        refine ⟨7188067850576766871869127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9584090467435689162492169 7188067850576766871869127)
        ·
          refine ⟨10782101775865150307803691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7188067850576766871869127 10782101775865150307803691)
          ·
            refine ⟨16173152663797725461705537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10782101775865150307803691 16173152663797725461705537)
            ·
              refine ⟨12129864497848294096279153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16173152663797725461705537 12129864497848294096279153)
              ·
                refine ⟨9097398373386220572209365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12129864497848294096279153 9097398373386220572209365)
                ·
                  refine ⟨213220274376239544661157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9097398373386220572209365 213220274376239544661157)
                  ·
                    rfl

theorem cell23_3737205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 2, 2, 7].length) (baseStart_3737205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3737205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3737205 prefixEnd_3737205 := by exact prefixLift 3737205
  have htrace : WordTrace (prefixWord ++ tailWord_3737205) baseStart_3737205 baseEnd_3737205 := by
    simpa [prefixWord, tailWord_3737205, baseEnd_3737205] using wordTrace_append hprefix tailTrace_3737205
  have hstable : (prefixWord ++ tailWord_3737205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3737205).length < 2 ^ (prefixWord ++ tailWord_3737205).sum := by decide
  have hdescent : baseEnd_3737205 < baseStart_3737205 := by decide
  rcases family_descends (prefixWord ++ tailWord_3737205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3737228 : List Nat := [2, 2, 1, 2, 1, 1, 4, 2, 1, 2, 5]
def baseStart_3737228 : Nat := 118140960795 + 3737228 * 2 ^ 59
def prefixEnd_3737228 : Nat := 4983230072969 + 3 ^ 40 * 3737228 * 2
def baseEnd_3737228 : Nat := 1918994279441209311962807

theorem tailTrace_3737228 : CollatzResearch.WordTrace tailWord_3737228 prefixEnd_3737228 1918994279441209311962807 := by
  unfold tailWord_3737228
  simp only [CollatzResearch.WordTrace]
  refine ⟨68153951652334349286210169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90871935536445799048280225 68153951652334349286210169)
  ·
    refine ⟨51115463739250761964657627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68153951652334349286210169 51115463739250761964657627)
    ·
      refine ⟨76673195608876142946986441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51115463739250761964657627 76673195608876142946986441)
      ·
        refine ⟨57504896706657107210239831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76673195608876142946986441 57504896706657107210239831)
        ·
          refine ⟨86257345059985660815359747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57504896706657107210239831 86257345059985660815359747)
          ·
            refine ⟨129386017589978491223039621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86257345059985660815359747 129386017589978491223039621)
            ·
              refine ⟨24259878298120967104319929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 129386017589978491223039621 24259878298120967104319929)
              ·
                refine ⟨18194908723590725328239947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24259878298120967104319929 18194908723590725328239947)
                ·
                  refine ⟨27292363085386087992359921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18194908723590725328239947 27292363085386087992359921)
                  ·
                    refine ⟨20469272314039565994269941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27292363085386087992359921 20469272314039565994269941)
                    ·
                      refine ⟨1918994279441209311962807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20469272314039565994269941 1918994279441209311962807)
                      ·
                        rfl

theorem cell23_3737228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 4, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 4, 2, 1, 2, 5].length) (baseStart_3737228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3737228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3737228 prefixEnd_3737228 := by exact prefixLift 3737228
  have htrace : WordTrace (prefixWord ++ tailWord_3737228) baseStart_3737228 baseEnd_3737228 := by
    simpa [prefixWord, tailWord_3737228, baseEnd_3737228] using wordTrace_append hprefix tailTrace_3737228
  have hstable : (prefixWord ++ tailWord_3737228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3737228).length < 2 ^ (prefixWord ++ tailWord_3737228).sum := by decide
  have hdescent : baseEnd_3737228 < baseStart_3737228 := by decide
  rcases family_descends (prefixWord ++ tailWord_3737228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3737250 : List Nat := [3, 3, 1, 4, 1, 2, 2, 1, 2, 2, 2]
def baseStart_3737250 : Nat := 118140960795 + 3737250 * 2 ^ 59
def prefixEnd_3737250 : Nat := 4983230072969 + 3 ^ 40 * 3737250 * 2
def baseEnd_3737250 : Nat := 1919005576015608225887707

theorem tailTrace_3737250 : CollatzResearch.WordTrace tailWord_3737250 prefixEnd_3737250 1919005576015608225887707 := by
  unfold tailWord_3737250
  simp only [CollatzResearch.WordTrace]
  refine ⟨34077176427647249082430301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90872470473725997553147469 34077176427647249082430301)
  ·
    refine ⟨12778941160367718405911363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34077176427647249082430301 12778941160367718405911363)
    ·
      refine ⟨19168411740551577608867045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12778941160367718405911363 19168411740551577608867045)
      ·
        refine ⟨3594077201353420801662571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19168411740551577608867045 3594077201353420801662571)
        ·
          refine ⟨5391115802030131202493857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3594077201353420801662571 5391115802030131202493857)
          ·
            refine ⟨4043336851522598401870393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5391115802030131202493857 4043336851522598401870393)
            ·
              refine ⟨3032502638641948801402795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4043336851522598401870393 3032502638641948801402795)
              ·
                refine ⟨4548753957962923202104193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3032502638641948801402795 4548753957962923202104193)
                ·
                  refine ⟨3411565468472192401578145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4548753957962923202104193 3411565468472192401578145)
                  ·
                    refine ⟨2558674101354144301183609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3411565468472192401578145 2558674101354144301183609)
                    ·
                      refine ⟨1919005576015608225887707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2558674101354144301183609 1919005576015608225887707)
                      ·
                        rfl

theorem cell23_3737250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 2, 2, 1, 2, 2, 2].length) (baseStart_3737250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3737250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3737250 prefixEnd_3737250 := by exact prefixLift 3737250
  have htrace : WordTrace (prefixWord ++ tailWord_3737250) baseStart_3737250 baseEnd_3737250 := by
    simpa [prefixWord, tailWord_3737250, baseEnd_3737250] using wordTrace_append hprefix tailTrace_3737250
  have hstable : (prefixWord ++ tailWord_3737250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3737250).length < 2 ^ (prefixWord ++ tailWord_3737250).sum := by decide
  have hdescent : baseEnd_3737250 < baseStart_3737250 := by decide
  rcases family_descends (prefixWord ++ tailWord_3737250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3737322 : List Nat := [3, 1, 3, 1, 1, 1, 3, 1, 5, 1, 3]
def baseStart_3737322 : Nat := 118140960795 + 3737322 * 2 ^ 59
def prefixEnd_3737322 : Nat := 4983230072969 + 3 ^ 40 * 3737322 * 2
def baseEnd_3737322 : Nat := 1919042546622731944187375

theorem tailTrace_3737322 : CollatzResearch.WordTrace tailWord_3737322 prefixEnd_3737322 1919042546622731944187375 := by
  unfold tailWord_3737322
  simp only [CollatzResearch.WordTrace]
  refine ⟨34077832941582038156585555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90874221177552101750894813 34077832941582038156585555)
  ·
    refine ⟨51116749412373057234878333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34077832941582038156585555 51116749412373057234878333)
    ·
      refine ⟨19168781029639896463079375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51116749412373057234878333 19168781029639896463079375)
      ·
        refine ⟨28753171544459844694619063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19168781029639896463079375 28753171544459844694619063)
        ·
          refine ⟨43129757316689767041928595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28753171544459844694619063 43129757316689767041928595)
          ·
            refine ⟨64694635975034650562892893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43129757316689767041928595 64694635975034650562892893)
            ·
              refine ⟨24260488490637993961084835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64694635975034650562892893 24260488490637993961084835)
              ·
                refine ⟨36390732735956990941627253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24260488490637993961084835 36390732735956990941627253)
                ·
                  refine ⟨3411631193995967900777555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 36390732735956990941627253 3411631193995967900777555)
                  ·
                    refine ⟨5117446790993951851166333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3411631193995967900777555 5117446790993951851166333)
                    ·
                      refine ⟨1919042546622731944187375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5117446790993951851166333 1919042546622731944187375)
                      ·
                        rfl

theorem cell23_3737322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 3, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 3, 1, 5, 1, 3].length) (baseStart_3737322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3737322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3737322 prefixEnd_3737322 := by exact prefixLift 3737322
  have htrace : WordTrace (prefixWord ++ tailWord_3737322) baseStart_3737322 baseEnd_3737322 := by
    simpa [prefixWord, tailWord_3737322, baseEnd_3737322] using wordTrace_append hprefix tailTrace_3737322
  have hstable : (prefixWord ++ tailWord_3737322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3737322).length < 2 ^ (prefixWord ++ tailWord_3737322).sum := by decide
  have hdescent : baseEnd_3737322 < baseStart_3737322 := by decide
  rcases family_descends (prefixWord ++ tailWord_3737322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3737365 : List Nat := [1, 3, 2, 1, 2, 3, 1, 1, 3, 1, 5]
def baseStart_3737365 : Nat := 118140960795 + 3737365 * 2 ^ 59
def prefixEnd_3737365 : Nat := 4983230072969 + 3 ^ 40 * 3737365 * 2
def baseEnd_3737365 : Nat := 1919064626290875275949677

theorem tailTrace_3737365 : CollatzResearch.WordTrace tailWord_3737365 prefixEnd_3737365 1919064626290875275949677 := by
  unfold tailWord_3737365
  simp only [CollatzResearch.WordTrace]
  refine ⟨136312900105172370970157549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90875266736781580646771699 136312900105172370970157549)
  ·
    refine ⟨51117337539439639113809081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 136312900105172370970157549 51117337539439639113809081)
    ·
      refine ⟨38338003154579729335356811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51117337539439639113809081 38338003154579729335356811)
      ·
        refine ⟨57507004731869594003035217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38338003154579729335356811 57507004731869594003035217)
        ·
          refine ⟨43130253548902195502276413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57507004731869594003035217 43130253548902195502276413)
          ·
            refine ⟨16173845080838323313353655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43130253548902195502276413 16173845080838323313353655)
            ·
              refine ⟨24260767621257484970030483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16173845080838323313353655 24260767621257484970030483)
              ·
                refine ⟨36391151431886227455045725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24260767621257484970030483 36391151431886227455045725)
                ·
                  refine ⟨13646681786957335295642147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36391151431886227455045725 13646681786957335295642147)
                  ·
                    refine ⟨20470022680436002943463221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13646681786957335295642147 20470022680436002943463221)
                    ·
                      refine ⟨1919064626290875275949677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20470022680436002943463221 1919064626290875275949677)
                      ·
                        rfl

theorem cell23_3737365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 1, 1, 3, 1, 5].length) (baseStart_3737365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3737365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3737365 prefixEnd_3737365 := by exact prefixLift 3737365
  have htrace : WordTrace (prefixWord ++ tailWord_3737365) baseStart_3737365 baseEnd_3737365 := by
    simpa [prefixWord, tailWord_3737365, baseEnd_3737365] using wordTrace_append hprefix tailTrace_3737365
  have hstable : (prefixWord ++ tailWord_3737365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3737365).length < 2 ^ (prefixWord ++ tailWord_3737365).sum := by decide
  have hdescent : baseEnd_3737365 < baseStart_3737365 := by decide
  rcases family_descends (prefixWord ++ tailWord_3737365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
