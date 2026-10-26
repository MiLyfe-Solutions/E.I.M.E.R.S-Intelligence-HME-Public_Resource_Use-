import V185TrunkScan23Chunk1250

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_7409431 : List Nat := [1, 1, 3, 4, 2, 2, 2, 1, 7]
def baseStart_7409431 : Nat := 118140960795 + 7409431 * 2 ^ 59
def prefixEnd_7409431 : Nat := 4983230072969 + 3 ^ 40 * 7409431 * 2
def baseEnd_7409431 : Nat := 422733275480411700093017

theorem tailTrace_7409431 : CollatzResearch.WordTrace tailWord_7409431 prefixEnd_7409431 422733275480411700093017 := by
  unfold tailWord_7409431
  simp only [CollatzResearch.WordTrace]
  refine ⟨270244150019904391913876147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180162766679936261275917431 270244150019904391913876147)
  ·
    refine ⟨405366225029856587870814221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270244150019904391913876147 405366225029856587870814221)
    ·
      refine ⟨152012334386196220451555333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 405366225029856587870814221 152012334386196220451555333)
      ·
        refine ⟨28502312697411791334666625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 152012334386196220451555333 28502312697411791334666625)
        ·
          refine ⟨21376734523058843500999969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28502312697411791334666625 21376734523058843500999969)
          ·
            refine ⟨16032550892294132625749977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21376734523058843500999969 16032550892294132625749977)
            ·
              refine ⟨12024413169220599469312483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16032550892294132625749977 12024413169220599469312483)
              ·
                refine ⟨18036619753830899203968725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12024413169220599469312483 18036619753830899203968725)
                ·
                  refine ⟨422733275480411700093017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18036619753830899203968725 422733275480411700093017)
                  ·
                    rfl

theorem cell23_7409431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 2, 1, 7].length) (baseStart_7409431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7409431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7409431 prefixEnd_7409431 := by exact prefixLift 7409431
  have htrace : WordTrace (prefixWord ++ tailWord_7409431) baseStart_7409431 baseEnd_7409431 := by
    simpa [prefixWord, tailWord_7409431, baseEnd_7409431] using wordTrace_append hprefix tailTrace_7409431
  have hstable : (prefixWord ++ tailWord_7409431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7409431).length < 2 ^ (prefixWord ++ tailWord_7409431).sum := by decide
  have hdescent : baseEnd_7409431 < baseStart_7409431 := by decide
  rcases family_descends (prefixWord ++ tailWord_7409431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7409441 : List Nat := [1, 2, 3, 2, 1, 3, 2, 1, 2, 3, 3]
def baseStart_7409441 : Nat := 118140960795 + 7409441 * 2 ^ 59
def prefixEnd_7409441 : Nat := 4983230072969 + 3 ^ 40 * 7409441 * 2
def baseEnd_7409441 : Nat := 3804604614130250261712107

theorem tailTrace_7409441 : CollatzResearch.WordTrace tailWord_7409441 prefixEnd_7409441 3804604614130250261712107 := by
  unfold tailWord_7409441
  simp only [CollatzResearch.WordTrace]
  refine ⟨270244514749868163621740177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180163009833245442414493451 270244514749868163621740177)
  ·
    refine ⟨202683386062401122716305133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 270244514749868163621740177 202683386062401122716305133)
    ·
      refine ⟨76006269773400421018614425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 202683386062401122716305133 76006269773400421018614425)
      ·
        refine ⟨57004702330050315763960819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76006269773400421018614425 57004702330050315763960819)
        ·
          refine ⟨85507053495075473645941229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57004702330050315763960819 85507053495075473645941229)
          ·
            refine ⟨32065145060653302617227961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 85507053495075473645941229 32065145060653302617227961)
            ·
              refine ⟨24048858795489976962920971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32065145060653302617227961 24048858795489976962920971)
              ·
                refine ⟨36073288193234965444381457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24048858795489976962920971 36073288193234965444381457)
                ·
                  refine ⟨27054966144926224083286093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36073288193234965444381457 27054966144926224083286093)
                  ·
                    refine ⟨10145612304347334031232285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27054966144926224083286093 10145612304347334031232285)
                    ·
                      refine ⟨3804604614130250261712107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10145612304347334031232285 3804604614130250261712107)
                      ·
                        rfl

theorem cell23_7409441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 2, 1, 2, 3, 3].length) (baseStart_7409441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7409441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7409441 prefixEnd_7409441 := by exact prefixLift 7409441
  have htrace : WordTrace (prefixWord ++ tailWord_7409441) baseStart_7409441 baseEnd_7409441 := by
    simpa [prefixWord, tailWord_7409441, baseEnd_7409441] using wordTrace_append hprefix tailTrace_7409441
  have hstable : (prefixWord ++ tailWord_7409441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7409441).length < 2 ^ (prefixWord ++ tailWord_7409441).sum := by decide
  have hdescent : baseEnd_7409441 < baseStart_7409441 := by decide
  rcases family_descends (prefixWord ++ tailWord_7409441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7409442 : List Nat := [3, 3, 1, 1, 2, 1, 5, 1, 2, 2, 2]
def baseStart_7409442 : Nat := 118140960795 + 7409442 * 2 ^ 59
def prefixEnd_7409442 : Nat := 4983230072969 + 3 ^ 40 * 7409442 * 2
def baseEnd_7409442 : Nat := 3804605127610904757799603

theorem tailTrace_7409442 : CollatzResearch.WordTrace tailWord_7409442 prefixEnd_7409442 3804605127610904757799603 := by
  unfold tailWord_7409442
  simp only [CollatzResearch.WordTrace]
  refine ⟨67561137805716135198131645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 180163034148576360528351053 67561137805716135198131645)
  ·
    refine ⟨25335426677143550699299367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67561137805716135198131645 25335426677143550699299367)
    ·
      refine ⟨38003140015715326048949051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25335426677143550699299367 38003140015715326048949051)
      ·
        refine ⟨57004710023572989073423577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38003140015715326048949051 57004710023572989073423577)
        ·
          refine ⟨42753532517679741805067683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57004710023572989073423577 42753532517679741805067683)
          ·
            refine ⟨64130298776519612707601525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42753532517679741805067683 64130298776519612707601525)
            ·
              refine ⟨6012215510298713691337643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 64130298776519612707601525 6012215510298713691337643)
              ·
                refine ⟨9018323265448070537006465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6012215510298713691337643 9018323265448070537006465)
                ·
                  refine ⟨6763742449086052902754849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9018323265448070537006465 6763742449086052902754849)
                  ·
                    refine ⟨5072806836814539677066137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6763742449086052902754849 5072806836814539677066137)
                    ·
                      refine ⟨3804605127610904757799603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5072806836814539677066137 3804605127610904757799603)
                      ·
                        rfl

theorem cell23_7409442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 5, 1, 2, 2, 2].length) (baseStart_7409442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7409442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7409442 prefixEnd_7409442 := by exact prefixLift 7409442
  have htrace : WordTrace (prefixWord ++ tailWord_7409442) baseStart_7409442 baseEnd_7409442 := by
    simpa [prefixWord, tailWord_7409442, baseEnd_7409442] using wordTrace_append hprefix tailTrace_7409442
  have hstable : (prefixWord ++ tailWord_7409442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7409442).length < 2 ^ (prefixWord ++ tailWord_7409442).sum := by decide
  have hdescent : baseEnd_7409442 < baseStart_7409442 := by decide
  rcases family_descends (prefixWord ++ tailWord_7409442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7409481 : List Nat := [1, 2, 1, 1, 2, 4, 3, 2, 2, 1, 4]
def baseStart_7409481 : Nat := 118140960795 + 7409481 * 2 ^ 59
def prefixEnd_7409481 : Nat := 4983230072969 + 3 ^ 40 * 7409481 * 2
def baseEnd_7409481 : Nat := 3804625153356430105211923

theorem tailTrace_7409481 : CollatzResearch.WordTrace tailWord_7409481 prefixEnd_7409481 3804625153356430105211923 := by
  unfold tailWord_7409481
  simp only [CollatzResearch.WordTrace]
  refine ⟨270245973669723250453196297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180163982446482166968797531 270245973669723250453196297)
  ·
    refine ⟨202684480252292437839897223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 270245973669723250453196297 202684480252292437839897223)
    ·
      refine ⟨304026720378438656759845835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202684480252292437839897223 304026720378438656759845835)
      ·
        refine ⟨456040080567657985139768753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 304026720378438656759845835 456040080567657985139768753)
        ·
          refine ⟨342030060425743488854826565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 456040080567657985139768753 342030060425743488854826565)
          ·
            refine ⟨64130636329826904160279981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 342030060425743488854826565 64130636329826904160279981)
            ·
              refine ⟨24048988623685089060104993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64130636329826904160279981 24048988623685089060104993)
              ·
                refine ⟨18036741467763816795078745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24048988623685089060104993 18036741467763816795078745)
                ·
                  refine ⟨13527556100822862596309059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18036741467763816795078745 13527556100822862596309059)
                  ·
                    refine ⟨20291334151234293894463589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13527556100822862596309059 20291334151234293894463589)
                    ·
                      refine ⟨3804625153356430105211923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20291334151234293894463589 3804625153356430105211923)
                      ·
                        rfl

theorem cell23_7409481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 3, 2, 2, 1, 4].length) (baseStart_7409481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7409481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7409481 prefixEnd_7409481 := by exact prefixLift 7409481
  have htrace : WordTrace (prefixWord ++ tailWord_7409481) baseStart_7409481 baseEnd_7409481 := by
    simpa [prefixWord, tailWord_7409481, baseEnd_7409481] using wordTrace_append hprefix tailTrace_7409481
  have hstable : (prefixWord ++ tailWord_7409481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7409481).length < 2 ^ (prefixWord ++ tailWord_7409481).sum := by decide
  have hdescent : baseEnd_7409481 < baseStart_7409481 := by decide
  rcases family_descends (prefixWord ++ tailWord_7409481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7409525 : List Nat := [1, 3, 4, 1, 1, 1, 2, 5, 1, 4]
def baseStart_7409525 : Nat := 118140960795 + 7409525 * 2 ^ 59
def prefixEnd_7409525 : Nat := 4983230072969 + 3 ^ 40 * 7409525 * 2
def baseEnd_7409525 : Nat := 1268215915501742644353907

theorem tailTrace_7409525 : CollatzResearch.WordTrace tailWord_7409525 prefixEnd_7409525 1268215915501742644353907 := by
  unfold tailWord_7409525
  simp only [CollatzResearch.WordTrace]
  refine ⟨270247578481563845967798029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180165052321042563978532019 270247578481563845967798029)
  ·
    refine ⟨101342841930586442237924261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 270247578481563845967798029 101342841930586442237924261)
    ·
      refine ⟨19001782861984957919610799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 101342841930586442237924261 19001782861984957919610799)
      ·
        refine ⟨28502674292977436879416199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19001782861984957919610799 28502674292977436879416199)
        ·
          refine ⟨42754011439466155319124299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28502674292977436879416199 42754011439466155319124299)
          ·
            refine ⟨64131017159199232978686449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42754011439466155319124299 64131017159199232978686449)
            ·
              refine ⟨48098262869399424734014837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64131017159199232978686449 48098262869399424734014837)
              ·
                refine ⟨4509212144006196068813891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 48098262869399424734014837 4509212144006196068813891)
                ·
                  refine ⟨6763818216009294103220837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4509212144006196068813891 6763818216009294103220837)
                  ·
                    refine ⟨1268215915501742644353907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6763818216009294103220837 1268215915501742644353907)
                    ·
                      rfl

theorem cell23_7409525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 2, 5, 1, 4].length) (baseStart_7409525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7409525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7409525 prefixEnd_7409525 := by exact prefixLift 7409525
  have htrace : WordTrace (prefixWord ++ tailWord_7409525) baseStart_7409525 baseEnd_7409525 := by
    simpa [prefixWord, tailWord_7409525, baseEnd_7409525] using wordTrace_append hprefix tailTrace_7409525
  have hstable : (prefixWord ++ tailWord_7409525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7409525).length < 2 ^ (prefixWord ++ tailWord_7409525).sum := by decide
  have hdescent : baseEnd_7409525 < baseStart_7409525 := by decide
  rcases family_descends (prefixWord ++ tailWord_7409525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7409548 : List Nat := [2, 2, 1, 2, 1, 2, 1, 5, 3, 1, 3]
def baseStart_7409548 : Nat := 118140960795 + 7409548 * 2 ^ 59
def prefixEnd_7409548 : Nat := 4983230072969 + 3 ^ 40 * 7409548 * 2
def baseEnd_7409548 : Nat := 3804659556560281343074115

theorem tailTrace_7409548 : CollatzResearch.WordTrace tailWord_7409548 prefixEnd_7409548 3804659556560281343074115 := by
  unfold tailWord_7409548
  simp only [CollatzResearch.WordTrace]
  refine ⟨135124208680240260447942649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180165611573653680597256865 135124208680240260447942649)
  ·
    refine ⟨101343156510180195335956987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135124208680240260447942649 101343156510180195335956987)
    ·
      refine ⟨152014734765270293003935481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101343156510180195335956987 152014734765270293003935481)
      ·
        refine ⟨114011051073952719752951611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 152014734765270293003935481 114011051073952719752951611)
        ·
          refine ⟨171016576610929079629427417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114011051073952719752951611 171016576610929079629427417)
          ·
            refine ⟨128262432458196809722070563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 171016576610929079629427417 128262432458196809722070563)
            ·
              refine ⟨192393648687295214583105845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 128262432458196809722070563 192393648687295214583105845)
              ·
                refine ⟨18036904564433926367166173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 192393648687295214583105845 18036904564433926367166173)
                ·
                  refine ⟨6763839211662722387687315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18036904564433926367166173 6763839211662722387687315)
                  ·
                    refine ⟨10145758817494083581530973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6763839211662722387687315 10145758817494083581530973)
                    ·
                      refine ⟨3804659556560281343074115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10145758817494083581530973 3804659556560281343074115)
                      ·
                        rfl

theorem cell23_7409548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 5, 3, 1, 3].length) (baseStart_7409548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7409548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7409548 prefixEnd_7409548 := by exact prefixLift 7409548
  have htrace : WordTrace (prefixWord ++ tailWord_7409548) baseStart_7409548 baseEnd_7409548 := by
    simpa [prefixWord, tailWord_7409548, baseEnd_7409548] using wordTrace_append hprefix tailTrace_7409548
  have hstable : (prefixWord ++ tailWord_7409548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7409548).length < 2 ^ (prefixWord ++ tailWord_7409548).sum := by decide
  have hdescent : baseEnd_7409548 < baseStart_7409548 := by decide
  rcases family_descends (prefixWord ++ tailWord_7409548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7409565 : List Nat := [1, 4, 2, 1, 2, 3, 1, 2, 3, 1, 3]
def baseStart_7409565 : Nat := 118140960795 + 7409565 * 2 ^ 59
def prefixEnd_7409565 : Nat := 4983230072969 + 3 ^ 40 * 7409565 * 2
def baseEnd_7409565 : Nat := 3804668285731407776561537

theorem tailTrace_7409565 : CollatzResearch.WordTrace tailWord_7409565 prefixEnd_7409565 3804668285731407776561537 := by
  unfold tailWord_7409565
  simp only [CollatzResearch.WordTrace]
  refine ⟨270249037401418932799254149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180166024934279288532836099 270249037401418932799254149)
  ·
    refine ⟨50671694512766049899860153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 270249037401418932799254149 50671694512766049899860153)
    ·
      refine ⟨38003770884574537424895115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50671694512766049899860153 38003770884574537424895115)
      ·
        refine ⟨57005656326861806137342673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38003770884574537424895115 57005656326861806137342673)
        ·
          refine ⟨42754242245146354603007005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57005656326861806137342673 42754242245146354603007005)
          ·
            refine ⟨16032840841929882976127627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42754242245146354603007005 16032840841929882976127627)
            ·
              refine ⟨24049261262894824464191441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16032840841929882976127627 24049261262894824464191441)
              ·
                refine ⟨18036945947171118348143581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24049261262894824464191441 18036945947171118348143581)
                ·
                  refine ⟨6763854730189169380553843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18036945947171118348143581 6763854730189169380553843)
                  ·
                    refine ⟨10145782095283754070830765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6763854730189169380553843 10145782095283754070830765)
                    ·
                      refine ⟨3804668285731407776561537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10145782095283754070830765 3804668285731407776561537)
                      ·
                        rfl

theorem cell23_7409565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 1, 2, 3, 1, 3].length) (baseStart_7409565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7409565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7409565 prefixEnd_7409565 := by exact prefixLift 7409565
  have htrace : WordTrace (prefixWord ++ tailWord_7409565) baseStart_7409565 baseEnd_7409565 := by
    simpa [prefixWord, tailWord_7409565, baseEnd_7409565] using wordTrace_append hprefix tailTrace_7409565
  have hstable : (prefixWord ++ tailWord_7409565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7409565).length < 2 ^ (prefixWord ++ tailWord_7409565).sum := by decide
  have hdescent : baseEnd_7409565 < baseStart_7409565 := by decide
  rcases family_descends (prefixWord ++ tailWord_7409565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7409575 : List Nat := [1, 1, 6, 1, 2, 2, 1, 1, 1, 5, 2]
def baseStart_7409575 : Nat := 118140960795 + 7409575 * 2 ^ 59
def prefixEnd_7409575 : Nat := 4983230072969 + 3 ^ 40 * 7409575 * 2
def baseEnd_7409575 : Nat := 3804673420537952737436491

theorem tailTrace_7409575 : CollatzResearch.WordTrace tailWord_7409575 prefixEnd_7409575 3804673420537952737436491 := by
  unfold tailWord_7409575
  simp only [CollatzResearch.WordTrace]
  refine ⟨270249402131382704507118179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180166268087588469671412119 270249402131382704507118179)
  ·
    refine ⟨405374103197074056760677269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270249402131382704507118179 405374103197074056760677269)
    ·
      refine ⟨19001911087362846410656747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 405374103197074056760677269 19001911087362846410656747)
      ·
        refine ⟨28502866631044269615985121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19001911087362846410656747 28502866631044269615985121)
        ·
          refine ⟨21377149973283202211988841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28502866631044269615985121 21377149973283202211988841)
          ·
            refine ⟨16032862479962401658991631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21377149973283202211988841 16032862479962401658991631)
            ·
              refine ⟨24049293719943602488487447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16032862479962401658991631 24049293719943602488487447)
              ·
                refine ⟨36073940579915403732731171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24049293719943602488487447 36073940579915403732731171)
                ·
                  refine ⟨54110910869873105599096757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36073940579915403732731171 54110910869873105599096757)
                  ·
                    refine ⟨5072897894050603649915321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 54110910869873105599096757 5072897894050603649915321)
                    ·
                      refine ⟨3804673420537952737436491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5072897894050603649915321 3804673420537952737436491)
                      ·
                        rfl

theorem cell23_7409575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 1, 1, 1, 5, 2].length) (baseStart_7409575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7409575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7409575 prefixEnd_7409575 := by exact prefixLift 7409575
  have htrace : WordTrace (prefixWord ++ tailWord_7409575) baseStart_7409575 baseEnd_7409575 := by
    simpa [prefixWord, tailWord_7409575, baseEnd_7409575] using wordTrace_append hprefix tailTrace_7409575
  have hstable : (prefixWord ++ tailWord_7409575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7409575).length < 2 ^ (prefixWord ++ tailWord_7409575).sum := by decide
  have hdescent : baseEnd_7409575 < baseStart_7409575 := by decide
  rcases family_descends (prefixWord ++ tailWord_7409575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7409585 : List Nat := [1, 2, 2, 4, 2, 1, 4, 1, 1, 5]
def baseStart_7409585 : Nat := 118140960795 + 7409585 * 2 ^ 59
def prefixEnd_7409585 : Nat := 4983230072969 + 3 ^ 40 * 7409585 * 2
def baseEnd_7409585 : Nat := 1268226185114832566103815

theorem tailTrace_7409585 : CollatzResearch.WordTrace tailWord_7409585 prefixEnd_7409585 1268226185114832566103815 := by
  unfold tailWord_7409585
  simp only [CollatzResearch.WordTrace]
  refine ⟨270249766861346476214982209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180166511240897650809988139 270249766861346476214982209)
  ·
    refine ⟨202687325146009857161236657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 270249766861346476214982209 202687325146009857161236657)
    ·
      refine ⟨152015493859507392870927493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 202687325146009857161236657 152015493859507392870927493)
      ·
        refine ⟨28502905098657636163298905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 152015493859507392870927493 28502905098657636163298905)
        ·
          refine ⟨21377178823993227122474179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28502905098657636163298905 21377178823993227122474179)
          ·
            refine ⟨32065768235989840683711269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21377178823993227122474179 32065768235989840683711269)
            ·
              refine ⟨6012331544248095128195863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32065768235989840683711269 6012331544248095128195863)
              ·
                refine ⟨9018497316372142692293795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6012331544248095128195863 9018497316372142692293795)
                ·
                  refine ⟨13527745974558214038440693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9018497316372142692293795 13527745974558214038440693)
                  ·
                    refine ⟨1268226185114832566103815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13527745974558214038440693 1268226185114832566103815)
                    ·
                      rfl

theorem cell23_7409585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 4, 1, 1, 5].length) (baseStart_7409585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7409585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7409585 prefixEnd_7409585 := by exact prefixLift 7409585
  have htrace : WordTrace (prefixWord ++ tailWord_7409585) baseStart_7409585 baseEnd_7409585 := by
    simpa [prefixWord, tailWord_7409585, baseEnd_7409585] using wordTrace_append hprefix tailTrace_7409585
  have hstable : (prefixWord ++ tailWord_7409585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7409585).length < 2 ^ (prefixWord ++ tailWord_7409585).sum := by decide
  have hdescent : baseEnd_7409585 < baseStart_7409585 := by decide
  rcases family_descends (prefixWord ++ tailWord_7409585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7409591 : List Nat := [1, 1, 3, 1, 3, 1, 1, 5, 1, 1, 5]
def baseStart_7409591 : Nat := 118140960795 + 7409591 * 2 ^ 59
def prefixEnd_7409591 : Nat := 4983230072969 + 3 ^ 40 * 7409591 * 2
def baseEnd_7409591 : Nat := 3804681636228424674836417

theorem tailTrace_7409591 : CollatzResearch.WordTrace tailWord_7409591 prefixEnd_7409591 3804681636228424674836417 := by
  unfold tailWord_7409591
  simp only [CollatzResearch.WordTrace]
  refine ⟨270249985699324739239700627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180166657132883159493133751 270249985699324739239700627)
  ·
    refine ⟨405374978548987108859550941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270249985699324739239700627 405374978548987108859550941)
    ·
      refine ⟨152015616955870165822331603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 405374978548987108859550941 152015616955870165822331603)
      ·
        refine ⟨228023425433805248733497405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152015616955870165822331603 228023425433805248733497405)
        ·
          refine ⟨85508784537676968275061527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 228023425433805248733497405 85508784537676968275061527)
          ·
            refine ⟨128263176806515452412592291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85508784537676968275061527 128263176806515452412592291)
            ·
              refine ⟨192394765209773178618888437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 128263176806515452412592291 192394765209773178618888437)
              ·
                refine ⟨18037009238416235495520791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 192394765209773178618888437 18037009238416235495520791)
                ·
                  refine ⟨27055513857624353243281187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18037009238416235495520791 27055513857624353243281187)
                  ·
                    refine ⟨40583270786436529864921781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27055513857624353243281187 40583270786436529864921781)
                    ·
                      refine ⟨3804681636228424674836417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40583270786436529864921781 3804681636228424674836417)
                      ·
                        rfl

theorem cell23_7409591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 5, 1, 1, 5].length) (baseStart_7409591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7409591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7409591 prefixEnd_7409591 := by exact prefixLift 7409591
  have htrace : WordTrace (prefixWord ++ tailWord_7409591) baseStart_7409591 baseEnd_7409591 := by
    simpa [prefixWord, tailWord_7409591, baseEnd_7409591] using wordTrace_append hprefix tailTrace_7409591
  have hstable : (prefixWord ++ tailWord_7409591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7409591).length < 2 ^ (prefixWord ++ tailWord_7409591).sum := by decide
  have hdescent : baseEnd_7409591 < baseStart_7409591 := by decide
  rcases family_descends (prefixWord ++ tailWord_7409591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7409608 : List Nat := [2, 1, 3, 1, 4, 2, 1, 2, 1, 1, 5]
def baseStart_7409608 : Nat := 118140960795 + 7409608 * 2 ^ 59
def prefixEnd_7409608 : Nat := 4983230072969 + 3 ^ 40 * 7409608 * 2
def baseEnd_7409608 : Nat := 3804690365399551108323839

theorem tailTrace_7409608 : CollatzResearch.WordTrace tailWord_7409608 prefixEnd_7409608 3804690365399551108323839 := by
  unfold tailWord_7409608
  simp only [CollatzResearch.WordTrace]
  refine ⟨135125302870131575571534739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180167070493508767428712985 135125302870131575571534739)
  ·
    refine ⟨202687954305197363357302109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135125302870131575571534739 202687954305197363357302109)
    ·
      refine ⟨76007982864449011258988291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 202687954305197363357302109 76007982864449011258988291)
      ·
        refine ⟨114011974296673516888482437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76007982864449011258988291 114011974296673516888482437)
        ·
          refine ⟨21377245180626284416590457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 114011974296673516888482437 21377245180626284416590457)
          ·
            refine ⟨16032933885469713312442843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21377245180626284416590457 16032933885469713312442843)
            ·
              refine ⟨24049400828204569968664265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16032933885469713312442843 24049400828204569968664265)
              ·
                refine ⟨18037050621153427476498199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24049400828204569968664265 18037050621153427476498199)
                ·
                  refine ⟨27055575931730141214747299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18037050621153427476498199 27055575931730141214747299)
                  ·
                    refine ⟨40583363897595211822120949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27055575931730141214747299 40583363897595211822120949)
                    ·
                      refine ⟨3804690365399551108323839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40583363897595211822120949 3804690365399551108323839)
                      ·
                        rfl

theorem cell23_7409608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 1, 2, 1, 1, 5].length) (baseStart_7409608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7409608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7409608 prefixEnd_7409608 := by exact prefixLift 7409608
  have htrace : WordTrace (prefixWord ++ tailWord_7409608) baseStart_7409608 baseEnd_7409608 := by
    simpa [prefixWord, tailWord_7409608, baseEnd_7409608] using wordTrace_append hprefix tailTrace_7409608
  have hstable : (prefixWord ++ tailWord_7409608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7409608).length < 2 ^ (prefixWord ++ tailWord_7409608).sum := by decide
  have hdescent : baseEnd_7409608 < baseStart_7409608 := by decide
  rcases family_descends (prefixWord ++ tailWord_7409608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7409615 : List Nat := [1, 1, 2, 1, 1, 5, 5, 1, 2, 4]
def baseStart_7409615 : Nat := 118140960795 + 7409615 * 2 ^ 59
def prefixEnd_7409615 : Nat := 4983230072969 + 3 ^ 40 * 7409615 * 2
def baseEnd_7409615 : Nat := 1268231319921377526978769

theorem tailTrace_7409615 : CollatzResearch.WordTrace tailWord_7409615 prefixEnd_7409615 1268231319921377526978769 := by
  unfold tailWord_7409615
  simp only [CollatzResearch.WordTrace]
  refine ⟨270250861051237791338574299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180167240700825194225716199 270250861051237791338574299)
  ·
    refine ⟨405376291576856687007861449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270250861051237791338574299 405376291576856687007861449)
    ·
      refine ⟨304032218682642515255896087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 405376291576856687007861449 304032218682642515255896087)
      ·
        refine ⟨456048328023963772883844131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 304032218682642515255896087 456048328023963772883844131)
        ·
          refine ⟨684072492035945659325766197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 456048328023963772883844131 684072492035945659325766197)
          ·
            refine ⟨64131796128369905561790581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 684072492035945659325766197 64131796128369905561790581)
            ·
              refine ⟨6012355887034678646417867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 64131796128369905561790581 6012355887034678646417867)
              ·
                refine ⟨9018533830552017969626801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6012355887034678646417867 9018533830552017969626801)
                ·
                  refine ⟨6763900372914013477220101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9018533830552017969626801 6763900372914013477220101)
                  ·
                    refine ⟨1268231319921377526978769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6763900372914013477220101 1268231319921377526978769)
                    ·
                      rfl

theorem cell23_7409615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 5, 1, 2, 4].length) (baseStart_7409615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7409615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7409615 prefixEnd_7409615 := by exact prefixLift 7409615
  have htrace : WordTrace (prefixWord ++ tailWord_7409615) baseStart_7409615 baseEnd_7409615 := by
    simpa [prefixWord, tailWord_7409615, baseEnd_7409615] using wordTrace_append hprefix tailTrace_7409615
  have hstable : (prefixWord ++ tailWord_7409615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7409615).length < 2 ^ (prefixWord ++ tailWord_7409615).sum := by decide
  have hdescent : baseEnd_7409615 < baseStart_7409615 := by decide
  rcases family_descends (prefixWord ++ tailWord_7409615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7409645 : List Nat := [1, 5, 1, 4, 1, 2, 9]
def baseStart_7409645 : Nat := 118140960795 + 7409645 * 2 ^ 59
def prefixEnd_7409645 : Nat := 4983230072969 + 3 ^ 40 * 7409645 * 2
def baseEnd_7409645 : Nat := 46971720545478610661249

theorem tailTrace_7409645 : CollatzResearch.WordTrace tailWord_7409645 prefixEnd_7409645 46971720545478610661249 := by
  unfold tailWord_7409645
  simp only [CollatzResearch.WordTrace]
  refine ⟨270251955241129106462166389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180167970160752737641444259 270251955241129106462166389)
  ·
    refine ⟨25336120803855853730828099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 270251955241129106462166389 25336120803855853730828099)
    ·
      refine ⟨38004181205783780596242149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25336120803855853730828099 38004181205783780596242149)
      ·
        refine ⟨7125783976084458861795403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38004181205783780596242149 7125783976084458861795403)
        ·
          refine ⟨10688675964126688292693105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7125783976084458861795403 10688675964126688292693105)
          ·
            refine ⟨8016506973095016219519829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10688675964126688292693105 8016506973095016219519829)
            ·
              refine ⟨46971720545478610661249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8016506973095016219519829 46971720545478610661249)
              ·
                rfl

theorem cell23_7409645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 2, 9].length) (baseStart_7409645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7409645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7409645 prefixEnd_7409645 := by exact prefixLift 7409645
  have htrace : WordTrace (prefixWord ++ tailWord_7409645) baseStart_7409645 baseEnd_7409645 := by
    simpa [prefixWord, tailWord_7409645, baseEnd_7409645] using wordTrace_append hprefix tailTrace_7409645
  have hstable : (prefixWord ++ tailWord_7409645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7409645).length < 2 ^ (prefixWord ++ tailWord_7409645).sum := by decide
  have hdescent : baseEnd_7409645 < baseStart_7409645 := by decide
  rcases family_descends (prefixWord ++ tailWord_7409645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7409665 : List Nat := [1, 2, 4, 1, 2, 1, 2, 2, 3, 3, 2]
def baseStart_7409665 : Nat := 118140960795 + 7409665 * 2 ^ 59
def prefixEnd_7409665 : Nat := 4983230072969 + 3 ^ 40 * 7409665 * 2
def baseEnd_7409665 : Nat := 3804719633796857385311077

theorem tailTrace_7409665 : CollatzResearch.WordTrace tailWord_7409665 prefixEnd_7409665 3804719633796857385311077 := by
  unfold tailWord_7409665
  simp only [CollatzResearch.WordTrace]
  refine ⟨270252684701056649877894449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180168456467371099918596299 270252684701056649877894449)
  ·
    refine ⟨202689513525792487408420837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 270252684701056649877894449 202689513525792487408420837)
    ·
      refine ⟨38004283786086091389078907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 202689513525792487408420837 38004283786086091389078907)
      ·
        refine ⟨57006425679129137083618361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38004283786086091389078907 57006425679129137083618361)
        ·
          refine ⟨42754819259346852812713771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57006425679129137083618361 42754819259346852812713771)
          ·
            refine ⟨64132228889020279219070657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42754819259346852812713771 64132228889020279219070657)
            ·
              refine ⟨48099171666765209414302993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64132228889020279219070657 48099171666765209414302993)
              ·
                refine ⟨36074378750073907060727245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48099171666765209414302993 36074378750073907060727245)
                ·
                  refine ⟨13527892031277715147772717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36074378750073907060727245 13527892031277715147772717)
                  ·
                    refine ⟨5072959511729143180414769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13527892031277715147772717 5072959511729143180414769)
                    ·
                      refine ⟨3804719633796857385311077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5072959511729143180414769 3804719633796857385311077)
                      ·
                        rfl

theorem cell23_7409665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 2, 2, 3, 3, 2].length) (baseStart_7409665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7409665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7409665 prefixEnd_7409665 := by exact prefixLift 7409665
  have htrace : WordTrace (prefixWord ++ tailWord_7409665) baseStart_7409665 baseEnd_7409665 := by
    simpa [prefixWord, tailWord_7409665, baseEnd_7409665] using wordTrace_append hprefix tailTrace_7409665
  have hstable : (prefixWord ++ tailWord_7409665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7409665).length < 2 ^ (prefixWord ++ tailWord_7409665).sum := by decide
  have hdescent : baseEnd_7409665 < baseStart_7409665 := by decide
  rcases family_descends (prefixWord ++ tailWord_7409665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7409691 : List Nat := [1, 1, 1, 1, 1, 1, 3, 3, 3, 4, 4]
def baseStart_7409691 : Nat := 118140960795 + 7409691 * 2 ^ 59
def prefixEnd_7409691 : Nat := 4983230072969 + 3 ^ 40 * 7409691 * 2
def baseEnd_7409691 : Nat := 3804732984293874283585957

theorem tailTrace_7409691 : CollatzResearch.WordTrace tailWord_7409691 prefixEnd_7409691 3804732984293874283585957 := by
  unfold tailWord_7409691
  simp only [CollatzResearch.WordTrace]
  refine ⟨270253632998962456318340927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180169088665974970878893951 270253632998962456318340927)
  ·
    refine ⟨405380449498443684477511391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270253632998962456318340927 405380449498443684477511391)
    ·
      refine ⟨608070674247665526716267087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 405380449498443684477511391 608070674247665526716267087)
      ·
        refine ⟨912106011371498290074400631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 608070674247665526716267087 912106011371498290074400631)
        ·
          refine ⟨1368159017057247435111600947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 912106011371498290074400631 1368159017057247435111600947)
          ·
            refine ⟨2052238525585871152667401421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1368159017057247435111600947 2052238525585871152667401421)
            ·
              refine ⟨769589447094701682250275533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2052238525585871152667401421 769589447094701682250275533)
              ·
                refine ⟨288596042660513130843853325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 769589447094701682250275533 288596042660513130843853325)
                ·
                  refine ⟨108223515997692424066444997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 288596042660513130843853325 108223515997692424066444997)
                  ·
                    refine ⟨20291909249567329512458437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 108223515997692424066444997 20291909249567329512458437)
                    ·
                      refine ⟨3804732984293874283585957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20291909249567329512458437 3804732984293874283585957)
                      ·
                        rfl

theorem cell23_7409691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 3, 4, 4].length) (baseStart_7409691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7409691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7409691 prefixEnd_7409691 := by exact prefixLift 7409691
  have htrace : WordTrace (prefixWord ++ tailWord_7409691) baseStart_7409691 baseEnd_7409691 := by
    simpa [prefixWord, tailWord_7409691, baseEnd_7409691] using wordTrace_append hprefix tailTrace_7409691
  have hstable : (prefixWord ++ tailWord_7409691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7409691).length < 2 ^ (prefixWord ++ tailWord_7409691).sum := by decide
  have hdescent : baseEnd_7409691 < baseStart_7409691 := by decide
  rcases family_descends (prefixWord ++ tailWord_7409691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7409695 : List Nat := [1, 1, 2, 4, 1, 2, 3, 2, 1, 4, 2]
def baseStart_7409695 : Nat := 118140960795 + 7409695 * 2 ^ 59
def prefixEnd_7409695 : Nat := 4983230072969 + 3 ^ 40 * 7409695 * 2
def baseEnd_7409695 : Nat := 3804735038216492267935939

theorem tailTrace_7409695 : CollatzResearch.WordTrace tailWord_7409695 prefixEnd_7409695 3804735038216492267935939 := by
  unfold tailWord_7409695
  simp only [CollatzResearch.WordTrace]
  refine ⟨270253778890947965001486539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180169185927298643334324359 270253778890947965001486539)
  ·
    refine ⟨405380668336421947502229809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270253778890947965001486539 405380668336421947502229809)
    ·
      refine ⟨304035501252316460626672357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 405380668336421947502229809 304035501252316460626672357)
      ·
        refine ⟨57006656484809336367501067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 304035501252316460626672357 57006656484809336367501067)
        ·
          refine ⟨85509984727214004551251601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57006656484809336367501067 85509984727214004551251601)
          ·
            refine ⟨64132488545410503413438701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85509984727214004551251601 64132488545410503413438701)
            ·
              refine ⟨24049683204528938780039513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64132488545410503413438701 24049683204528938780039513)
              ·
                refine ⟨18037262403396704085029635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24049683204528938780039513 18037262403396704085029635)
                ·
                  refine ⟨27055893605095056127544453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18037262403396704085029635 27055893605095056127544453)
                  ·
                    refine ⟨5072980050955323023914585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27055893605095056127544453 5072980050955323023914585)
                    ·
                      refine ⟨3804735038216492267935939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5072980050955323023914585 3804735038216492267935939)
                      ·
                        rfl

theorem cell23_7409695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 3, 2, 1, 4, 2].length) (baseStart_7409695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7409695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7409695 prefixEnd_7409695 := by exact prefixLift 7409695
  have htrace : WordTrace (prefixWord ++ tailWord_7409695) baseStart_7409695 baseEnd_7409695 := by
    simpa [prefixWord, tailWord_7409695, baseEnd_7409695] using wordTrace_append hprefix tailTrace_7409695
  have hstable : (prefixWord ++ tailWord_7409695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7409695).length < 2 ^ (prefixWord ++ tailWord_7409695).sum := by decide
  have hdescent : baseEnd_7409695 < baseStart_7409695 := by decide
  rcases family_descends (prefixWord ++ tailWord_7409695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7409698 : List Nat := [3, 3, 1, 1, 1, 2, 1, 3, 2, 1, 5]
def baseStart_7409698 : Nat := 118140960795 + 7409698 * 2 ^ 59
def prefixEnd_7409698 : Nat := 4983230072969 + 3 ^ 40 * 7409698 * 2
def baseEnd_7409698 : Nat := 3804736578658455756198425

theorem tailTrace_7409698 : CollatzResearch.WordTrace tailWord_7409698 prefixEnd_7409698 3804736578658455756198425 := by
  unfold tailWord_7409698
  simp only [CollatzResearch.WordTrace]
  refine ⟨67563472077484274128461437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 180169258873291397675897165 67563472077484274128461437)
  ·
    refine ⟨25336302029056602798173039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67563472077484274128461437 25336302029056602798173039)
    ·
      refine ⟨38004453043584904197259559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25336302029056602798173039 38004453043584904197259559)
      ·
        refine ⟨57006679565377356295889339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38004453043584904197259559 57006679565377356295889339)
        ·
          refine ⟨85510019348066034443834009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57006679565377356295889339 85510019348066034443834009)
          ·
            refine ⟨64132514511049525832875507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85510019348066034443834009 64132514511049525832875507)
            ·
              refine ⟨96198771766574288749313261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64132514511049525832875507 96198771766574288749313261)
              ·
                refine ⟨36074539412465358280992473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 96198771766574288749313261 36074539412465358280992473)
                ·
                  refine ⟨27055904559349018710744355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36074539412465358280992473 27055904559349018710744355)
                  ·
                    refine ⟨40583856839023528066116533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27055904559349018710744355 40583856839023528066116533)
                    ·
                      refine ⟨3804736578658455756198425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40583856839023528066116533 3804736578658455756198425)
                      ·
                        rfl

theorem cell23_7409698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 3, 2, 1, 5].length) (baseStart_7409698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7409698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7409698 prefixEnd_7409698 := by exact prefixLift 7409698
  have htrace : WordTrace (prefixWord ++ tailWord_7409698) baseStart_7409698 baseEnd_7409698 := by
    simpa [prefixWord, tailWord_7409698, baseEnd_7409698] using wordTrace_append hprefix tailTrace_7409698
  have hstable : (prefixWord ++ tailWord_7409698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7409698).length < 2 ^ (prefixWord ++ tailWord_7409698).sum := by decide
  have hdescent : baseEnd_7409698 < baseStart_7409698 := by decide
  rcases family_descends (prefixWord ++ tailWord_7409698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7409712 : List Nat := [2, 1, 1, 1, 2, 5, 1, 4, 2, 2, 2]
def baseStart_7409712 : Nat := 118140960795 + 7409712 * 2 ^ 59
def prefixEnd_7409712 : Nat := 4983230072969 + 3 ^ 40 * 7409712 * 2
def baseEnd_7409712 : Nat := 3804743767387618701423361

theorem tailTrace_7409712 : CollatzResearch.WordTrace tailWord_7409712 prefixEnd_7409712 3804743767387618701423361 := by
  unfold tailWord_7409712
  simp only [CollatzResearch.WordTrace]
  refine ⟨135127199465943188452427695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180169599287924251269903593 135127199465943188452427695)
  ·
    refine ⟨202690799198914782678641543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135127199465943188452427695 202690799198914782678641543)
    ·
      refine ⟨304036198798372174017962315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202690799198914782678641543 304036198798372174017962315)
      ·
        refine ⟨456054298197558261026943473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 304036198798372174017962315 456054298197558261026943473)
        ·
          refine ⟨342040723648168695770207605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 456054298197558261026943473 342040723648168695770207605)
          ·
            refine ⟨32066317842015815228456963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 342040723648168695770207605 32066317842015815228456963)
            ·
              refine ⟨48099476763023722842685445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32066317842015815228456963 48099476763023722842685445)
              ·
                refine ⟨9018651893066948033003521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48099476763023722842685445 9018651893066948033003521)
                ·
                  refine ⟨6763988919800211024752641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9018651893066948033003521 6763988919800211024752641)
                  ·
                    refine ⟨5072991689850158268564481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6763988919800211024752641 5072991689850158268564481)
                    ·
                      refine ⟨3804743767387618701423361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5072991689850158268564481 3804743767387618701423361)
                      ·
                        rfl

theorem cell23_7409712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 1, 4, 2, 2, 2].length) (baseStart_7409712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7409712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7409712 prefixEnd_7409712 := by exact prefixLift 7409712
  have htrace : WordTrace (prefixWord ++ tailWord_7409712) baseStart_7409712 baseEnd_7409712 := by
    simpa [prefixWord, tailWord_7409712, baseEnd_7409712] using wordTrace_append hprefix tailTrace_7409712
  have hstable : (prefixWord ++ tailWord_7409712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7409712).length < 2 ^ (prefixWord ++ tailWord_7409712).sum := by decide
  have hdescent : baseEnd_7409712 < baseStart_7409712 := by decide
  rcases family_descends (prefixWord ++ tailWord_7409712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7409728 : List Nat := [2, 1, 1, 2, 2, 4, 1, 1, 1, 5, 3]
def baseStart_7409728 : Nat := 118140960795 + 7409728 * 2 ^ 59
def prefixEnd_7409728 : Nat := 4983230072969 + 3 ^ 40 * 7409728 * 2
def baseEnd_7409728 : Nat := 3804751983078090638823287

theorem tailTrace_7409728 : CollatzResearch.WordTrace tailWord_7409728 prefixEnd_7409728 3804751983078090638823287 := by
  unfold tailWord_7409728
  simp only [CollatzResearch.WordTrace]
  refine ⟨135127491249914205818718919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180169988333218941091625225 135127491249914205818718919)
  ·
    refine ⟨202691236874871308728078379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135127491249914205818718919 202691236874871308728078379)
    ·
      refine ⟨304036855312306963092117569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202691236874871308728078379 304036855312306963092117569)
      ·
        refine ⟨228027641484230222319088177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 304036855312306963092117569 228027641484230222319088177)
        ·
          refine ⟨171020731113172666739316133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 228027641484230222319088177 171020731113172666739316133)
          ·
            refine ⟨32066387083719875013621775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 171020731113172666739316133 32066387083719875013621775)
            ·
              refine ⟨48099580625579812520432663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32066387083719875013621775 48099580625579812520432663)
              ·
                refine ⟨72149370938369718780648995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48099580625579812520432663 72149370938369718780648995)
                ·
                  refine ⟨108224056407554578170973493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 72149370938369718780648995 108224056407554578170973493)
                  ·
                    refine ⟨10146005288208241703528765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 108224056407554578170973493 10146005288208241703528765)
                    ·
                      refine ⟨3804751983078090638823287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10146005288208241703528765 3804751983078090638823287)
                      ·
                        rfl

theorem cell23_7409728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 1, 1, 1, 5, 3].length) (baseStart_7409728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7409728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7409728 prefixEnd_7409728 := by exact prefixLift 7409728
  have htrace : WordTrace (prefixWord ++ tailWord_7409728) baseStart_7409728 baseEnd_7409728 := by
    simpa [prefixWord, tailWord_7409728, baseEnd_7409728] using wordTrace_append hprefix tailTrace_7409728
  have hstable : (prefixWord ++ tailWord_7409728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7409728).length < 2 ^ (prefixWord ++ tailWord_7409728).sum := by decide
  have hdescent : baseEnd_7409728 < baseStart_7409728 := by decide
  rcases family_descends (prefixWord ++ tailWord_7409728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7409729 : List Nat := [1, 2, 5, 1, 2, 1, 2, 3, 2, 2, 2]
def baseStart_7409729 : Nat := 118140960795 + 7409729 * 2 ^ 59
def prefixEnd_7409729 : Nat := 4983230072969 + 3 ^ 40 * 7409729 * 2
def baseEnd_7409729 : Nat := 3804752496558745134910783

theorem tailTrace_7409729 : CollatzResearch.WordTrace tailWord_7409729 prefixEnd_7409729 3804752496558745134910783 := by
  unfold tailWord_7409729
  simp only [CollatzResearch.WordTrace]
  refine ⟨270255018972824788808224241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180170012648549859205482827 270255018972824788808224241)
  ·
    refine ⟨202691264229618591606168181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 270255018972824788808224241 202691264229618591606168181)
    ·
      refine ⟨19002306021526742963078267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 202691264229618591606168181 19002306021526742963078267)
      ·
        refine ⟨28503459032290114444617401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19002306021526742963078267 28503459032290114444617401)
        ·
          refine ⟨21377594274217585833463051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28503459032290114444617401 21377594274217585833463051)
          ·
            refine ⟨32066391411326378750194577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21377594274217585833463051 32066391411326378750194577)
            ·
              refine ⟨24049793558494784062645933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32066391411326378750194577 24049793558494784062645933)
              ·
                refine ⟨9018672584435544023492225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24049793558494784062645933 9018672584435544023492225)
                ·
                  refine ⟨6764004438326658017619169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9018672584435544023492225 6764004438326658017619169)
                  ·
                    refine ⟨5073003328744993513214377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6764004438326658017619169 5073003328744993513214377)
                    ·
                      refine ⟨3804752496558745134910783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5073003328744993513214377 3804752496558745134910783)
                      ·
                        rfl

theorem cell23_7409729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 2, 3, 2, 2, 2].length) (baseStart_7409729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7409729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7409729 prefixEnd_7409729 := by exact prefixLift 7409729
  have htrace : WordTrace (prefixWord ++ tailWord_7409729) baseStart_7409729 baseEnd_7409729 := by
    simpa [prefixWord, tailWord_7409729, baseEnd_7409729] using wordTrace_append hprefix tailTrace_7409729
  have hstable : (prefixWord ++ tailWord_7409729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7409729).length < 2 ^ (prefixWord ++ tailWord_7409729).sum := by decide
  have hdescent : baseEnd_7409729 < baseStart_7409729 := by decide
  rcases family_descends (prefixWord ++ tailWord_7409729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7409795 : List Nat := [1, 1, 1, 3, 3, 3, 2, 2, 3, 4]
def baseStart_7409795 : Nat := 118140960795 + 7409795 * 2 ^ 59
def prefixEnd_7409795 : Nat := 4983230072969 + 3 ^ 40 * 7409795 * 2
def baseEnd_7409795 : Nat := 1268262128760647292228493

theorem tailTrace_7409795 : CollatzResearch.WordTrace tailWord_7409795 prefixEnd_7409795 1268262128760647292228493 := by
  unfold tailWord_7409795
  simp only [CollatzResearch.WordTrace]
  refine ⟨270257426190585682080126839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180171617460390454720084559 270257426190585682080126839)
  ·
    refine ⟨405386139285878523120190259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270257426190585682080126839 405386139285878523120190259)
    ·
      refine ⟨608079208928817784680285389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 405386139285878523120190259 608079208928817784680285389)
      ·
        refine ⟨228029703348306669255107021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 608079208928817784680285389 228029703348306669255107021)
        ·
          refine ⟨85511138755615000970665133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 228029703348306669255107021 85511138755615000970665133)
          ·
            refine ⟨32066677033355625363999425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 85511138755615000970665133 32066677033355625363999425)
            ·
              refine ⟨24050007775016719022999569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32066677033355625363999425 24050007775016719022999569)
              ·
                refine ⟨18037505831262539267249677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24050007775016719022999569 18037505831262539267249677)
                ·
                  refine ⟨6764064686723452225218629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18037505831262539267249677 6764064686723452225218629)
                  ·
                    refine ⟨1268262128760647292228493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6764064686723452225218629 1268262128760647292228493)
                    ·
                      rfl

theorem cell23_7409795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 2, 2, 3, 4].length) (baseStart_7409795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7409795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7409795 prefixEnd_7409795 := by exact prefixLift 7409795
  have htrace : WordTrace (prefixWord ++ tailWord_7409795) baseStart_7409795 baseEnd_7409795 := by
    simpa [prefixWord, tailWord_7409795, baseEnd_7409795] using wordTrace_append hprefix tailTrace_7409795
  have hstable : (prefixWord ++ tailWord_7409795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7409795).length < 2 ^ (prefixWord ++ tailWord_7409795).sum := by decide
  have hdescent : baseEnd_7409795 < baseStart_7409795 := by decide
  rcases family_descends (prefixWord ++ tailWord_7409795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7409829 : List Nat := [1, 3, 1, 2, 1, 3, 5, 2, 1, 4]
def baseStart_7409829 : Nat := 118140960795 + 7409829 * 2 ^ 59
def prefixEnd_7409829 : Nat := 4983230072969 + 3 ^ 40 * 7409829 * 2
def baseEnd_7409829 : Nat := 1268267948208064914553441

theorem tailTrace_7409829 : CollatzResearch.WordTrace tailWord_7409829 prefixEnd_7409829 1268267948208064914553441 := by
  unfold tailWord_7409829
  simp only [CollatzResearch.WordTrace]
  refine ⟨270258666272462505886864541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180172444181641670591243027 270258666272462505886864541)
  ·
    refine ⟨101346999852173439707574203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 270258666272462505886864541 101346999852173439707574203)
    ·
      refine ⟨152020499778260159561361305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101346999852173439707574203 152020499778260159561361305)
      ·
        refine ⟨114015374833695119671020979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 152020499778260159561361305 114015374833695119671020979)
        ·
          refine ⟨171023062250542679506531469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114015374833695119671020979 171023062250542679506531469)
          ·
            refine ⟨64133648343953504814949301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 171023062250542679506531469 64133648343953504814949301)
            ·
              refine ⟨6012529532245641076401497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 64133648343953504814949301 6012529532245641076401497)
              ·
                refine ⟨4509397149184230807301123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6012529532245641076401497 4509397149184230807301123)
                ·
                  refine ⟨6764095723776346210951685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4509397149184230807301123 6764095723776346210951685)
                  ·
                    refine ⟨1268267948208064914553441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6764095723776346210951685 1268267948208064914553441)
                    ·
                      rfl

theorem cell23_7409829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 5, 2, 1, 4].length) (baseStart_7409829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7409829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7409829 prefixEnd_7409829 := by exact prefixLift 7409829
  have htrace : WordTrace (prefixWord ++ tailWord_7409829) baseStart_7409829 baseEnd_7409829 := by
    simpa [prefixWord, tailWord_7409829, baseEnd_7409829] using wordTrace_append hprefix tailTrace_7409829
  have hstable : (prefixWord ++ tailWord_7409829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7409829).length < 2 ^ (prefixWord ++ tailWord_7409829).sum := by decide
  have hdescent : baseEnd_7409829 < baseStart_7409829 := by decide
  rcases family_descends (prefixWord ++ tailWord_7409829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7409905 : List Nat := [1, 2, 2, 2, 2, 1, 3, 3, 1, 2, 4]
def baseStart_7409905 : Nat := 118140960795 + 7409905 * 2 ^ 59
def prefixEnd_7409905 : Nat := 4983230072969 + 3 ^ 40 * 7409905 * 2
def baseEnd_7409905 : Nat := 3804842869153936446309973

theorem tailTrace_7409905 : CollatzResearch.WordTrace tailWord_7409905 prefixEnd_7409905 3804842869153936446309973 := by
  unfold tailWord_7409905
  simp only [CollatzResearch.WordTrace]
  refine ⟨270261438220187170866631169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180174292146791447244420779 270261438220187170866631169)
  ·
    refine ⟨202696078665140378149973377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 270261438220187170866631169 202696078665140378149973377)
    ·
      refine ⟨152022058998855283612480033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 202696078665140378149973377 152022058998855283612480033)
      ·
        refine ⟨114016544249141462709360025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 152022058998855283612480033 114016544249141462709360025)
        ·
          refine ⟨85512408186856097032020019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114016544249141462709360025 85512408186856097032020019)
          ·
            refine ⟨128268612280284145548030029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85512408186856097032020019 128268612280284145548030029)
            ·
              refine ⟨48100729605106554580511261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 128268612280284145548030029 48100729605106554580511261)
              ·
                refine ⟨18037773601914957967691723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48100729605106554580511261 18037773601914957967691723)
                ·
                  refine ⟨27056660402872436951537585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18037773601914957967691723 27056660402872436951537585)
                  ·
                    refine ⟨20292495302154327713653189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27056660402872436951537585 20292495302154327713653189)
                    ·
                      refine ⟨3804842869153936446309973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20292495302154327713653189 3804842869153936446309973)
                      ·
                        rfl

theorem cell23_7409905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 3, 3, 1, 2, 4].length) (baseStart_7409905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7409905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7409905 prefixEnd_7409905 := by exact prefixLift 7409905
  have htrace : WordTrace (prefixWord ++ tailWord_7409905) baseStart_7409905 baseEnd_7409905 := by
    simpa [prefixWord, tailWord_7409905, baseEnd_7409905] using wordTrace_append hprefix tailTrace_7409905
  have hstable : (prefixWord ++ tailWord_7409905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7409905).length < 2 ^ (prefixWord ++ tailWord_7409905).sum := by decide
  have hdescent : baseEnd_7409905 < baseStart_7409905 := by decide
  rcases family_descends (prefixWord ++ tailWord_7409905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7409925 : List Nat := [1, 3, 1, 1, 2, 1, 2, 3, 3, 3, 3]
def baseStart_7409925 : Nat := 118140960795 + 7409925 * 2 ^ 59
def prefixEnd_7409925 : Nat := 4983230072969 + 3 ^ 40 * 7409925 * 2
def baseEnd_7409925 : Nat := 3804853138767026368059881

theorem tailTrace_7409925 : CollatzResearch.WordTrace tailWord_7409925 prefixEnd_7409925 3804853138767026368059881 := by
  unfold tailWord_7409925
  simp only [CollatzResearch.WordTrace]
  refine ⟨270262167680114714282359229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180174778453409809521572819 270262167680114714282359229)
  ·
    refine ⟨101348312880043017855884711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 270262167680114714282359229 101348312880043017855884711)
    ·
      refine ⟨152022469320064526783827067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101348312880043017855884711 152022469320064526783827067)
      ·
        refine ⟨228033703980096790175740601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152022469320064526783827067 228033703980096790175740601)
        ·
          refine ⟨171025277985072592631805451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 228033703980096790175740601 171025277985072592631805451)
          ·
            refine ⟨256537916977608888947708177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 171025277985072592631805451 256537916977608888947708177)
            ·
              refine ⟨192403437733206666710781133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 256537916977608888947708177 192403437733206666710781133)
              ·
                refine ⟨72151289149952500016542925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 192403437733206666710781133 72151289149952500016542925)
                ·
                  refine ⟨27056733431232187506203597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 72151289149952500016542925 27056733431232187506203597)
                  ·
                    refine ⟨10146275036712070314826349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27056733431232187506203597 10146275036712070314826349)
                    ·
                      refine ⟨3804853138767026368059881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10146275036712070314826349 3804853138767026368059881)
                      ·
                        rfl

theorem cell23_7409925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 3, 3, 3, 3].length) (baseStart_7409925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7409925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7409925 prefixEnd_7409925 := by exact prefixLift 7409925
  have htrace : WordTrace (prefixWord ++ tailWord_7409925) baseStart_7409925 baseEnd_7409925 := by
    simpa [prefixWord, tailWord_7409925, baseEnd_7409925] using wordTrace_append hprefix tailTrace_7409925
  have hstable : (prefixWord ++ tailWord_7409925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7409925).length < 2 ^ (prefixWord ++ tailWord_7409925).sum := by decide
  have hdescent : baseEnd_7409925 < baseStart_7409925 := by decide
  rcases family_descends (prefixWord ++ tailWord_7409925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7409929 : List Nat := [1, 2, 1, 1, 3, 4, 4, 1, 1, 2, 3]
def baseStart_7409929 : Nat := 118140960795 + 7409929 * 2 ^ 59
def prefixEnd_7409929 : Nat := 4983230072969 + 3 ^ 40 * 7409929 * 2
def baseEnd_7409929 : Nat := 3804855192689644352409863

theorem tailTrace_7409929 : CollatzResearch.WordTrace tailWord_7409929 prefixEnd_7409929 3804855192689644352409863 := by
  unfold tailWord_7409929
  simp only [CollatzResearch.WordTrace]
  refine ⟨270262313572100222965504841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180174875714733481977003227 270262313572100222965504841)
  ·
    refine ⟨202696735179075167224128631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 270262313572100222965504841 202696735179075167224128631)
    ·
      refine ⟨304045102768612750836192947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202696735179075167224128631 304045102768612750836192947)
      ·
        refine ⟨456067654152919126254289421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 304045102768612750836192947 456067654152919126254289421)
        ·
          refine ⟨171025370307344672345358533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 456067654152919126254289421 171025370307344672345358533)
          ·
            refine ⟨32067256932627126064754725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 171025370307344672345358533 32067256932627126064754725)
            ·
              refine ⟨6012610674867586137141511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32067256932627126064754725 6012610674867586137141511)
              ·
                refine ⟨9018916012301379205712267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6012610674867586137141511 9018916012301379205712267)
                ·
                  refine ⟨13528374018452068808568401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9018916012301379205712267 13528374018452068808568401)
                  ·
                    refine ⟨10146280513839051606426301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13528374018452068808568401 10146280513839051606426301)
                    ·
                      refine ⟨3804855192689644352409863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10146280513839051606426301 3804855192689644352409863)
                      ·
                        rfl

theorem cell23_7409929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 4, 1, 1, 2, 3].length) (baseStart_7409929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7409929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7409929 prefixEnd_7409929 := by exact prefixLift 7409929
  have htrace : WordTrace (prefixWord ++ tailWord_7409929) baseStart_7409929 baseEnd_7409929 := by
    simpa [prefixWord, tailWord_7409929, baseEnd_7409929] using wordTrace_append hprefix tailTrace_7409929
  have hstable : (prefixWord ++ tailWord_7409929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7409929).length < 2 ^ (prefixWord ++ tailWord_7409929).sum := by decide
  have hdescent : baseEnd_7409929 < baseStart_7409929 := by decide
  rcases family_descends (prefixWord ++ tailWord_7409929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7409966 : List Nat := [4, 1, 3, 3, 1, 2, 2, 7]
def baseStart_7409966 : Nat := 118140960795 + 7409966 * 2 ^ 59
def prefixEnd_7409966 : Nat := 4983230072969 + 3 ^ 40 * 7409966 * 2
def baseEnd_7409966 : Nat := 140921266350883729912859

theorem tailTrace_7409966 : CollatzResearch.WordTrace tailWord_7409966 prefixEnd_7409966 140921266350883729912859 := by
  unfold tailWord_7409966
  simp only [CollatzResearch.WordTrace]
  refine ⟨33782957884120772285575219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 180175775381977452189734501 33782957884120772285575219)
  ·
    refine ⟨50674436826181158428362829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33782957884120772285575219 50674436826181158428362829)
    ·
      refine ⟨19002913809817934410636061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50674436826181158428362829 19002913809817934410636061)
      ·
        refine ⟨7126092678681725403988523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19002913809817934410636061 7126092678681725403988523)
        ·
          refine ⟨10689139018022588105982785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7126092678681725403988523 10689139018022588105982785)
          ·
            refine ⟨8016854263516941079487089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10689139018022588105982785 8016854263516941079487089)
            ·
              refine ⟨6012640697637705809615317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8016854263516941079487089 6012640697637705809615317)
              ·
                refine ⟨140921266350883729912859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6012640697637705809615317 140921266350883729912859)
                ·
                  rfl

theorem cell23_7409966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 2, 2, 7].length) (baseStart_7409966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7409966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7409966 prefixEnd_7409966 := by exact prefixLift 7409966
  have htrace : WordTrace (prefixWord ++ tailWord_7409966) baseStart_7409966 baseEnd_7409966 := by
    simpa [prefixWord, tailWord_7409966, baseEnd_7409966] using wordTrace_append hprefix tailTrace_7409966
  have hstable : (prefixWord ++ tailWord_7409966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7409966).length < 2 ^ (prefixWord ++ tailWord_7409966).sum := by decide
  have hdescent : baseEnd_7409966 < baseStart_7409966 := by decide
  rcases family_descends (prefixWord ++ tailWord_7409966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7409972 : List Nat := [2, 5, 1, 1, 1, 2, 1, 1, 2, 2, 5]
def baseStart_7409972 : Nat := 118140960795 + 7409972 * 2 ^ 59
def prefixEnd_7409972 : Nat := 4983230072969 + 3 ^ 40 * 7409972 * 2
def baseEnd_7409972 : Nat := 3804877272357787684172165

theorem tailTrace_7409972 : CollatzResearch.WordTrace tailWord_7409972 prefixEnd_7409972 3804877272357787684172165 := by
  unfold tailWord_7409972
  simp only [CollatzResearch.WordTrace]
  refine ⟨135131940955472220654660085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180175921273962960872880113 135131940955472220654660085)
  ·
    refine ⟨12668619464575520686374383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 135131940955472220654660085 12668619464575520686374383)
    ·
      refine ⟨19002929196863281029561575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12668619464575520686374383 19002929196863281029561575)
      ·
        refine ⟨28504393795294921544342363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19002929196863281029561575 28504393795294921544342363)
        ·
          refine ⟨42756590692942382316513545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28504393795294921544342363 42756590692942382316513545)
          ·
            refine ⟨32067443019706786737385159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42756590692942382316513545 32067443019706786737385159)
            ·
              refine ⟨48101164529560180106077739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32067443019706786737385159 48101164529560180106077739)
              ·
                refine ⟨72151746794340270159116609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48101164529560180106077739 72151746794340270159116609)
                ·
                  refine ⟨54113810095755202619337457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 72151746794340270159116609 54113810095755202619337457)
                  ·
                    refine ⟨40585357571816401964503093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 54113810095755202619337457 40585357571816401964503093)
                    ·
                      refine ⟨3804877272357787684172165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40585357571816401964503093 3804877272357787684172165)
                      ·
                        rfl

theorem cell23_7409972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 1, 1, 2, 2, 5].length) (baseStart_7409972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7409972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7409972 prefixEnd_7409972 := by exact prefixLift 7409972
  have htrace : WordTrace (prefixWord ++ tailWord_7409972) baseStart_7409972 baseEnd_7409972 := by
    simpa [prefixWord, tailWord_7409972, baseEnd_7409972] using wordTrace_append hprefix tailTrace_7409972
  have hstable : (prefixWord ++ tailWord_7409972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7409972).length < 2 ^ (prefixWord ++ tailWord_7409972).sum := by decide
  have hdescent : baseEnd_7409972 < baseStart_7409972 := by decide
  rcases family_descends (prefixWord ++ tailWord_7409972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7409995 : List Nat := [1, 1, 1, 1, 3, 1, 1, 6, 2, 2, 4]
def baseStart_7409995 : Nat := 118140960795 + 7409995 * 2 ^ 59
def prefixEnd_7409995 : Nat := 4983230072969 + 3 ^ 40 * 7409995 * 2
def baseEnd_7409995 : Nat := 3804889082412841094184559

theorem tailTrace_7409995 : CollatzResearch.WordTrace tailWord_7409995 prefixEnd_7409995 3804889082412841094184559 := by
  unfold tailWord_7409995
  simp only [CollatzResearch.WordTrace]
  refine ⟨270264720789861116237407439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180176480526574077491604959 270264720789861116237407439)
  ·
    refine ⟨405397081184791674356111159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270264720789861116237407439 405397081184791674356111159)
    ·
      refine ⟨608095621777187511534166739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 405397081184791674356111159 608095621777187511534166739)
      ·
        refine ⟨912143432665781267301250109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 608095621777187511534166739 912143432665781267301250109)
        ·
          refine ⟨342053787249667975237968791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 912143432665781267301250109 342053787249667975237968791)
          ·
            refine ⟨513080680874501962856953187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 342053787249667975237968791 513080680874501962856953187)
            ·
              refine ⟨769621021311752944285429781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 513080680874501962856953187 769621021311752944285429781)
              ·
                refine ⟨36075985373988419263379521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 769621021311752944285429781 36075985373988419263379521)
                ·
                  refine ⟨27056989030491314447534641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36075985373988419263379521 27056989030491314447534641)
                  ·
                    refine ⟨20292741772868485835650981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27056989030491314447534641 20292741772868485835650981)
                    ·
                      refine ⟨3804889082412841094184559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20292741772868485835650981 3804889082412841094184559)
                      ·
                        rfl

theorem cell23_7409995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 6, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 6, 2, 2, 4].length) (baseStart_7409995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7409995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7409995 prefixEnd_7409995 := by exact prefixLift 7409995
  have htrace : WordTrace (prefixWord ++ tailWord_7409995) baseStart_7409995 baseEnd_7409995 := by
    simpa [prefixWord, tailWord_7409995, baseEnd_7409995] using wordTrace_append hprefix tailTrace_7409995
  have hstable : (prefixWord ++ tailWord_7409995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7409995).length < 2 ^ (prefixWord ++ tailWord_7409995).sum := by decide
  have hdescent : baseEnd_7409995 < baseStart_7409995 := by decide
  rcases family_descends (prefixWord ++ tailWord_7409995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7410014 : List Nat := [4, 4, 2, 1, 2, 1, 1, 2, 1, 2, 3]
def baseStart_7410014 : Nat := 118140960795 + 7410014 * 2 ^ 59
def prefixEnd_7410014 : Nat := 4983230072969 + 3 ^ 40 * 7410014 * 2
def baseEnd_7410014 : Nat := 3804898838545276519846973

theorem tailTrace_7410014 : CollatzResearch.WordTrace tailWord_7410014 prefixEnd_7410014 3804898838545276519846973 := by
  unfold tailWord_7410014
  simp only [CollatzResearch.WordTrace]
  refine ⟨33783176722099035310293637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 180176942517861521654899397 33783176722099035310293637)
  ·
    refine ⟨6334345635393569120680057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33783176722099035310293637 6334345635393569120680057)
    ·
      refine ⟨4750759226545176840510043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6334345635393569120680057 4750759226545176840510043)
      ·
        refine ⟨7126138839817765260765065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4750759226545176840510043 7126138839817765260765065)
        ·
          refine ⟨5344604129863323945573799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7126138839817765260765065 5344604129863323945573799)
          ·
            refine ⟨8016906194794985918360699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5344604129863323945573799 8016906194794985918360699)
            ·
              refine ⟨12025359292192478877541049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8016906194794985918360699 12025359292192478877541049)
              ·
                refine ⟨9019019469144359158155787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12025359292192478877541049 9019019469144359158155787)
                ·
                  refine ⟨13528529203716538737233681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9019019469144359158155787 13528529203716538737233681)
                  ·
                    refine ⟨10146396902787404052925261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13528529203716538737233681 10146396902787404052925261)
                    ·
                      refine ⟨3804898838545276519846973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10146396902787404052925261 3804898838545276519846973)
                      ·
                        rfl

theorem cell23_7410014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 2, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 2, 1, 1, 2, 1, 2, 3].length) (baseStart_7410014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7410014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7410014 prefixEnd_7410014 := by exact prefixLift 7410014
  have htrace : WordTrace (prefixWord ++ tailWord_7410014) baseStart_7410014 baseEnd_7410014 := by
    simpa [prefixWord, tailWord_7410014, baseEnd_7410014] using wordTrace_append hprefix tailTrace_7410014
  have hstable : (prefixWord ++ tailWord_7410014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7410014).length < 2 ^ (prefixWord ++ tailWord_7410014).sum := by decide
  have hdescent : baseEnd_7410014 < baseStart_7410014 := by decide
  rcases family_descends (prefixWord ++ tailWord_7410014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7410035 : List Nat := [1, 1, 1, 2, 2, 1, 2, 2, 6, 5]
def baseStart_7410035 : Nat := 118140960795 + 7410035 * 2 ^ 59
def prefixEnd_7410035 : Nat := 4983230072969 + 3 ^ 40 * 7410035 * 2
def baseEnd_7410035 : Nat := 1268303207213006979228125

theorem tailTrace_7410035 : CollatzResearch.WordTrace tailWord_7410035 prefixEnd_7410035 1268303207213006979228125 := by
  unfold tailWord_7410035
  simp only [CollatzResearch.WordTrace]
  refine ⟨270266179709716203068863559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180177453139810802045909039 270266179709716203068863559)
  ·
    refine ⟨405399269564574304603295339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270266179709716203068863559 405399269564574304603295339)
    ·
      refine ⟨608098904346861456904943009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 405399269564574304603295339 608098904346861456904943009)
      ·
        refine ⟨456074178260146092678707257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 608098904346861456904943009 456074178260146092678707257)
        ·
          refine ⟨342055633695109569509030443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 456074178260146092678707257 342055633695109569509030443)
          ·
            refine ⟨513083450542664354263545665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 342055633695109569509030443 513083450542664354263545665)
            ·
              refine ⟨384812587906998265697659249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 513083450542664354263545665 384812587906998265697659249)
              ·
                refine ⟨288609440930248699273244437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 384812587906998265697659249 288609440930248699273244437)
                ·
                  refine ⟨13528567543605407778433333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 288609440930248699273244437 13528567543605407778433333)
                  ·
                    refine ⟨1268303207213006979228125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13528567543605407778433333 1268303207213006979228125)
                    ·
                      rfl

theorem cell23_7410035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 2, 6, 5].length) (baseStart_7410035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7410035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7410035 prefixEnd_7410035 := by exact prefixLift 7410035
  have htrace : WordTrace (prefixWord ++ tailWord_7410035) baseStart_7410035 baseEnd_7410035 := by
    simpa [prefixWord, tailWord_7410035, baseEnd_7410035] using wordTrace_append hprefix tailTrace_7410035
  have hstable : (prefixWord ++ tailWord_7410035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7410035).length < 2 ^ (prefixWord ++ tailWord_7410035).sum := by decide
  have hdescent : baseEnd_7410035 < baseStart_7410035 := by decide
  rcases family_descends (prefixWord ++ tailWord_7410035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7410042 : List Nat := [3, 1, 1, 1, 1, 1, 2, 1, 3, 7, 2]
def baseStart_7410042 : Nat := 118140960795 + 7410042 * 2 ^ 59
def prefixEnd_7410042 : Nat := 4983230072969 + 3 ^ 40 * 7410042 * 2
def baseEnd_7410042 : Nat := 3804913216003602410296843

theorem tailTrace_7410042 : CollatzResearch.WordTrace tailWord_7410042 prefixEnd_7410042 3804913216003602410296843 := by
  unfold tailWord_7410042
  simp only [CollatzResearch.WordTrace]
  refine ⟨67566608755172710816092095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 180177623347127228842912253 67566608755172710816092095)
  ·
    refine ⟨101349913132759066224138143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67566608755172710816092095 101349913132759066224138143)
    ·
      refine ⟨152024869699138599336207215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101349913132759066224138143 152024869699138599336207215)
      ·
        refine ⟨228037304548707899004310823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152024869699138599336207215 228037304548707899004310823)
        ·
          refine ⟨342055956823061848506466235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 228037304548707899004310823 342055956823061848506466235)
          ·
            refine ⟨513083935234592772759699353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 342055956823061848506466235 513083935234592772759699353)
            ·
              refine ⟨384812951425944579569774515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 513083935234592772759699353 384812951425944579569774515)
              ·
                refine ⟨577219427138916869354661773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 384812951425944579569774515 577219427138916869354661773)
                ·
                  refine ⟨216457285177093826007998165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 577219427138916869354661773 216457285177093826007998165)
                  ·
                    refine ⟨5073217621338136547062457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 216457285177093826007998165 5073217621338136547062457)
                    ·
                      refine ⟨3804913216003602410296843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5073217621338136547062457 3804913216003602410296843)
                      ·
                        rfl

theorem cell23_7410042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 1, 3, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 1, 3, 7, 2].length) (baseStart_7410042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7410042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7410042 prefixEnd_7410042 := by exact prefixLift 7410042
  have htrace : WordTrace (prefixWord ++ tailWord_7410042) baseStart_7410042 baseEnd_7410042 := by
    simpa [prefixWord, tailWord_7410042, baseEnd_7410042] using wordTrace_append hprefix tailTrace_7410042
  have hstable : (prefixWord ++ tailWord_7410042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7410042).length < 2 ^ (prefixWord ++ tailWord_7410042).sum := by decide
  have hdescent : baseEnd_7410042 < baseStart_7410042 := by decide
  rcases family_descends (prefixWord ++ tailWord_7410042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7410052 : List Nat := [2, 3, 2, 1, 1, 2, 1, 4, 2, 5]
def baseStart_7410052 : Nat := 118140960795 + 7410052 * 2 ^ 59
def prefixEnd_7410052 : Nat := 4983230072969 + 3 ^ 40 * 7410052 * 2
def baseEnd_7410052 : Nat := 1268306116936715790390599

theorem tailTrace_7410052 : CollatzResearch.WordTrace tailWord_7410052 prefixEnd_7410052 1268306116936715790390599 := by
  unfold tailWord_7410052
  simp only [CollatzResearch.WordTrace]
  refine ⟨135133399875327307486116205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180177866500436409981488273 135133399875327307486116205)
  ·
    refine ⟨50675024953247740307293577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 135133399875327307486116205 50675024953247740307293577)
    ·
      refine ⟨38006268714935805230470183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50675024953247740307293577 38006268714935805230470183)
      ·
        refine ⟨57009403072403707845705275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38006268714935805230470183 57009403072403707845705275)
        ·
          refine ⟨85514104608605561768557913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57009403072403707845705275 85514104608605561768557913)
          ·
            refine ⟨64135578456454171326418435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85514104608605561768557913 64135578456454171326418435)
            ·
              refine ⟨96203367684681256989627653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64135578456454171326418435 96203367684681256989627653)
              ·
                refine ⟨18038131440877735685555185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 96203367684681256989627653 18038131440877735685555185)
                ·
                  refine ⟨13528598580658301764166389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18038131440877735685555185 13528598580658301764166389)
                  ·
                    refine ⟨1268306116936715790390599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13528598580658301764166389 1268306116936715790390599)
                    ·
                      rfl

theorem cell23_7410052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 4, 2, 5].length) (baseStart_7410052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7410052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7410052 prefixEnd_7410052 := by exact prefixLift 7410052
  have htrace : WordTrace (prefixWord ++ tailWord_7410052) baseStart_7410052 baseEnd_7410052 := by
    simpa [prefixWord, tailWord_7410052, baseEnd_7410052] using wordTrace_append hprefix tailTrace_7410052
  have hstable : (prefixWord ++ tailWord_7410052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7410052).length < 2 ^ (prefixWord ++ tailWord_7410052).sum := by decide
  have hdescent : baseEnd_7410052 < baseStart_7410052 := by decide
  rcases family_descends (prefixWord ++ tailWord_7410052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7410090 : List Nat := [3, 1, 6, 1, 1, 1, 2, 3, 5]
def baseStart_7410090 : Nat := 118140960795 + 7410090 * 2 ^ 59
def prefixEnd_7410090 : Nat := 4983230072969 + 3 ^ 40 * 7410090 * 2
def baseEnd_7410090 : Nat := 422770873675002024721847

theorem tailTrace_7410090 : CollatzResearch.WordTrace tailWord_7410090 prefixEnd_7410090 422770873675002024721847 := by
  unfold tailWord_7410090
  simp only [CollatzResearch.WordTrace]
  refine ⟨67567046431129236865528931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 180178790483011298308077149 67567046431129236865528931)
  ·
    refine ⟨101350569646693855298293397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67567046431129236865528931 101350569646693855298293397)
    ·
      refine ⟨4750807952188774467107503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 101350569646693855298293397 4750807952188774467107503)
      ·
        refine ⟨7126211928283161700661255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4750807952188774467107503 7126211928283161700661255)
        ·
          refine ⟨10689317892424742550991883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7126211928283161700661255 10689317892424742550991883)
          ·
            refine ⟨16033976838637113826487825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10689317892424742550991883 16033976838637113826487825)
            ·
              refine ⟨12025482628977835369865869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16033976838637113826487825 12025482628977835369865869)
              ·
                refine ⟨4509555985866688263699701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12025482628977835369865869 4509555985866688263699701)
                ·
                  refine ⟨422770873675002024721847, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4509555985866688263699701 422770873675002024721847)
                  ·
                    rfl

theorem cell23_7410090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 2, 3, 5].length) (baseStart_7410090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7410090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7410090 prefixEnd_7410090 := by exact prefixLift 7410090
  have htrace : WordTrace (prefixWord ++ tailWord_7410090) baseStart_7410090 baseEnd_7410090 := by
    simpa [prefixWord, tailWord_7410090, baseEnd_7410090] using wordTrace_append hprefix tailTrace_7410090
  have hstable : (prefixWord ++ tailWord_7410090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7410090).length < 2 ^ (prefixWord ++ tailWord_7410090).sum := by decide
  have hdescent : baseEnd_7410090 < baseStart_7410090 := by decide
  rcases family_descends (prefixWord ++ tailWord_7410090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7410202 : List Nat := [3, 1, 1, 3, 1, 1, 4, 9]
def baseStart_7410202 : Nat := 118140960795 + 7410202 * 2 ^ 59
def prefixEnd_7410202 : Nat := 4983230072969 + 3 ^ 40 * 7410202 * 2
def baseEnd_7410202 : Nat := 140925754552160066085041

theorem tailTrace_7410202 : CollatzResearch.WordTrace tailWord_7410202 prefixEnd_7410202 140925754552160066085041 := by
  unfold tailWord_7410202
  simp only [CollatzResearch.WordTrace]
  refine ⟨67568067675027797647548215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 180181513800074127060128573 67568067675027797647548215)
  ·
    refine ⟨101352101512541696471322323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67568067675027797647548215 101352101512541696471322323)
    ·
      refine ⟨152028152268812544706983485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101352101512541696471322323 152028152268812544706983485)
      ·
        refine ⟨57010557100804704265118807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 152028152268812544706983485 57010557100804704265118807)
        ·
          refine ⟨85515835651207056397678211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57010557100804704265118807 85515835651207056397678211)
          ·
            refine ⟨128273753476810584596517317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85515835651207056397678211 128273753476810584596517317)
            ·
              refine ⟨24051328776901984611846997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 128273753476810584596517317 24051328776901984611846997)
              ·
                refine ⟨140925754552160066085041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 24051328776901984611846997 140925754552160066085041)
                ·
                  rfl

theorem cell23_7410202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 4, 9].length) (baseStart_7410202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7410202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7410202 prefixEnd_7410202 := by exact prefixLift 7410202
  have htrace : WordTrace (prefixWord ++ tailWord_7410202) baseStart_7410202 baseEnd_7410202 := by
    simpa [prefixWord, tailWord_7410202, baseEnd_7410202] using wordTrace_append hprefix tailTrace_7410202
  have hstable : (prefixWord ++ tailWord_7410202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7410202).length < 2 ^ (prefixWord ++ tailWord_7410202).sum := by decide
  have hdescent : baseEnd_7410202 < baseStart_7410202 := by decide
  rcases family_descends (prefixWord ++ tailWord_7410202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7410209 : List Nat := [1, 2, 3, 2, 2, 1, 3, 2, 1, 2, 4]
def baseStart_7410209 : Nat := 118140960795 + 7410209 * 2 ^ 59
def prefixEnd_7410209 : Nat := 4983230072969 + 3 ^ 40 * 7410209 * 2
def baseEnd_7410209 : Nat := 3804998967272903256908575

theorem tailTrace_7410209 : CollatzResearch.WordTrace tailWord_7410209 prefixEnd_7410209 3804998967272903256908575 := by
  unfold tailWord_7410209
  simp only [CollatzResearch.WordTrace]
  refine ⟨270272526011085830785697681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180181684007390553857131787 270272526011085830785697681)
  ·
    refine ⟨202704394508314373089273261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 270272526011085830785697681 202704394508314373089273261)
    ·
      refine ⟨76014147940617889908477473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 202704394508314373089273261 76014147940617889908477473)
      ·
        refine ⟨57010610955463417431358105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76014147940617889908477473 57010610955463417431358105)
        ·
          refine ⟨42757958216597563073518579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57010610955463417431358105 42757958216597563073518579)
          ·
            refine ⟨64136937324896344610277869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42757958216597563073518579 64136937324896344610277869)
            ·
              refine ⟨24051351496836129228854201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64136937324896344610277869 24051351496836129228854201)
              ·
                refine ⟨18038513622627096921640651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24051351496836129228854201 18038513622627096921640651)
                ·
                  refine ⟨27057770433940645382460977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18038513622627096921640651 27057770433940645382460977)
                  ·
                    refine ⟨20293327825455484036845733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27057770433940645382460977 20293327825455484036845733)
                    ·
                      refine ⟨3804998967272903256908575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20293327825455484036845733 3804998967272903256908575)
                      ·
                        rfl

theorem cell23_7410209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 3, 2, 1, 2, 4].length) (baseStart_7410209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7410209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7410209 prefixEnd_7410209 := by exact prefixLift 7410209
  have htrace : WordTrace (prefixWord ++ tailWord_7410209) baseStart_7410209 baseEnd_7410209 := by
    simpa [prefixWord, tailWord_7410209, baseEnd_7410209] using wordTrace_append hprefix tailTrace_7410209
  have hstable : (prefixWord ++ tailWord_7410209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7410209).length < 2 ^ (prefixWord ++ tailWord_7410209).sum := by decide
  have hdescent : baseEnd_7410209 < baseStart_7410209 := by decide
  rcases family_descends (prefixWord ++ tailWord_7410209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7410216 : List Nat := [2, 1, 5, 2, 1, 1, 3, 1, 1, 1, 5]
def baseStart_7410216 : Nat := 118140960795 + 7410216 * 2 ^ 59
def prefixEnd_7410216 : Nat := 4983230072969 + 3 ^ 40 * 7410216 * 2
def baseEnd_7410216 : Nat := 3805002561637484729521043

theorem tailTrace_7410216 : CollatzResearch.WordTrace tailWord_7410216 prefixEnd_7410216 3805002561637484729521043 := by
  unfold tailWord_7410216
  simp only [CollatzResearch.WordTrace]
  refine ⟨135136390661030235490601251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180181854214706980654135001 135136390661030235490601251)
  ·
    refine ⟨202704585991545353235901877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135136390661030235490601251 202704585991545353235901877)
    ·
      refine ⟨19003554936707376865865801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 202704585991545353235901877 19003554936707376865865801)
      ·
        refine ⟨14252666202530532649399351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19003554936707376865865801 14252666202530532649399351)
        ·
          refine ⟨21378999303795798974099027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14252666202530532649399351 21378999303795798974099027)
          ·
            refine ⟨32068498955693698461148541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21378999303795798974099027 32068498955693698461148541)
            ·
              refine ⟨12025687108385136922930703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32068498955693698461148541 12025687108385136922930703)
              ·
                refine ⟨18038530662577705384396055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12025687108385136922930703 18038530662577705384396055)
                ·
                  refine ⟨27057795993866558076594083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18038530662577705384396055 27057795993866558076594083)
                  ·
                    refine ⟨40586693990799837114891125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27057795993866558076594083 40586693990799837114891125)
                    ·
                      refine ⟨3805002561637484729521043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40586693990799837114891125 3805002561637484729521043)
                      ·
                        rfl

theorem cell23_7410216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 3, 1, 1, 1, 5].length) (baseStart_7410216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7410216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7410216 prefixEnd_7410216 := by exact prefixLift 7410216
  have htrace : WordTrace (prefixWord ++ tailWord_7410216) baseStart_7410216 baseEnd_7410216 := by
    simpa [prefixWord, tailWord_7410216, baseEnd_7410216] using wordTrace_append hprefix tailTrace_7410216
  have hstable : (prefixWord ++ tailWord_7410216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7410216).length < 2 ^ (prefixWord ++ tailWord_7410216).sum := by decide
  have hdescent : baseEnd_7410216 < baseStart_7410216 := by decide
  rcases family_descends (prefixWord ++ tailWord_7410216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7410229 : List Nat := [1, 3, 3, 1, 1, 2, 1, 2, 3, 3, 3]
def baseStart_7410229 : Nat := 118140960795 + 7410229 * 2 ^ 59
def prefixEnd_7410229 : Nat := 4983230072969 + 3 ^ 40 * 7410229 * 2
def baseEnd_7410229 : Nat := 3805009236885993178658483

theorem tailTrace_7410229 : CollatzResearch.WordTrace tailWord_7410229 prefixEnd_7410229 3805009236885993178658483 := by
  unfold tailWord_7410229
  simp only [CollatzResearch.WordTrace]
  refine ⟨270273255471013374201425741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180182170314008916134283827 270273255471013374201425741)
  ·
    refine ⟨101352470801630015325534653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 270273255471013374201425741 101352470801630015325534653)
    ·
      refine ⟨38007176550611255747075495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 101352470801630015325534653 38007176550611255747075495)
      ·
        refine ⟨57010764825916883620613243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38007176550611255747075495 57010764825916883620613243)
        ·
          refine ⟨85516147238875325430919865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57010764825916883620613243 85516147238875325430919865)
          ·
            refine ⟨64137110429156494073189899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85516147238875325430919865 64137110429156494073189899)
            ·
              refine ⟨96205665643734741109784849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64137110429156494073189899 96205665643734741109784849)
              ·
                refine ⟨72154249232801055832338637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 96205665643734741109784849 72154249232801055832338637)
                ·
                  refine ⟨27057843462300395937126989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 72154249232801055832338637 27057843462300395937126989)
                  ·
                    refine ⟨10146691298362648476422621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27057843462300395937126989 10146691298362648476422621)
                    ·
                      refine ⟨3805009236885993178658483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10146691298362648476422621 3805009236885993178658483)
                      ·
                        rfl

theorem cell23_7410229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 2, 3, 3, 3].length) (baseStart_7410229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7410229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7410229 prefixEnd_7410229 := by exact prefixLift 7410229
  have htrace : WordTrace (prefixWord ++ tailWord_7410229) baseStart_7410229 baseEnd_7410229 := by
    simpa [prefixWord, tailWord_7410229, baseEnd_7410229] using wordTrace_append hprefix tailTrace_7410229
  have hstable : (prefixWord ++ tailWord_7410229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7410229).length < 2 ^ (prefixWord ++ tailWord_7410229).sum := by decide
  have hdescent : baseEnd_7410229 < baseStart_7410229 := by decide
  rcases family_descends (prefixWord ++ tailWord_7410229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7410232 : List Nat := [2, 1, 2, 1, 4, 1, 1, 1, 1, 9]
def baseStart_7410232 : Nat := 118140960795 + 7410232 * 2 ^ 59
def prefixEnd_7410232 : Nat := 4983230072969 + 3 ^ 40 * 7410232 * 2
def baseEnd_7410232 : Nat := 1268336925775985555640323

theorem tailTrace_7410232 : CollatzResearch.WordTrace tailWord_7410232 prefixEnd_7410232 1268336925775985555640323 := by
  unfold tailWord_7410232
  simp only [CollatzResearch.WordTrace]
  refine ⟨135136682445001252856892475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180182243260001670475856633 135136682445001252856892475)
  ·
    refine ⟨202705023667501879285338713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135136682445001252856892475 202705023667501879285338713)
    ·
      refine ⟨152028767750626409464004035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 202705023667501879285338713 152028767750626409464004035)
      ·
        refine ⟨228043151625939614196006053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152028767750626409464004035 228043151625939614196006053)
        ·
          refine ⟨42758090929863677661751135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 228043151625939614196006053 42758090929863677661751135)
          ·
            refine ⟨64137136394795516492626703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42758090929863677661751135 64137136394795516492626703)
            ·
              refine ⟨96205704592193274738940055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64137136394795516492626703 96205704592193274738940055)
              ·
                refine ⟨144308556888289912108410083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 96205704592193274738940055 144308556888289912108410083)
                ·
                  refine ⟨216462835332434868162615125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 144308556888289912108410083 216462835332434868162615125)
                  ·
                    refine ⟨1268336925775985555640323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 216462835332434868162615125 1268336925775985555640323)
                    ·
                      rfl

theorem cell23_7410232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 1, 1, 9].length) (baseStart_7410232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7410232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7410232 prefixEnd_7410232 := by exact prefixLift 7410232
  have htrace : WordTrace (prefixWord ++ tailWord_7410232) baseStart_7410232 baseEnd_7410232 := by
    simpa [prefixWord, tailWord_7410232, baseEnd_7410232] using wordTrace_append hprefix tailTrace_7410232
  have hstable : (prefixWord ++ tailWord_7410232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7410232).length < 2 ^ (prefixWord ++ tailWord_7410232).sum := by decide
  have hdescent : baseEnd_7410232 < baseStart_7410232 := by decide
  rcases family_descends (prefixWord ++ tailWord_7410232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7410273 : List Nat := [1, 2, 3, 1, 1, 5, 1, 3, 1, 3, 2]
def baseStart_7410273 : Nat := 118140960795 + 7410273 * 2 ^ 59
def prefixEnd_7410273 : Nat := 4983230072969 + 3 ^ 40 * 7410273 * 2
def baseEnd_7410273 : Nat := 3805031830034791006508281

theorem tailTrace_7410273 : CollatzResearch.WordTrace tailWord_7410273 prefixEnd_7410273 3805031830034791006508281 := by
  unfold tailWord_7410273
  simp only [CollatzResearch.WordTrace]
  refine ⟨270274860282853969716027473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180183240188569313144018315 270274860282853969716027473)
  ·
    refine ⟨202706145212140477287020605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 270274860282853969716027473 202706145212140477287020605)
    ·
      refine ⟨76014804454552678982632727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 202706145212140477287020605 76014804454552678982632727)
      ·
        refine ⟨114022206681829018473949091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76014804454552678982632727 114022206681829018473949091)
        ·
          refine ⟨171033310022743527710923637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114022206681829018473949091 171033310022743527710923637)
          ·
            refine ⟨16034372814632205722899091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 171033310022743527710923637 16034372814632205722899091)
            ·
              refine ⟨24051559221948308584348637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16034372814632205722899091 24051559221948308584348637)
              ·
                refine ⟨9019334708230615719130739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24051559221948308584348637 9019334708230615719130739)
                ·
                  refine ⟨13529002062345923578696109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9019334708230615719130739 13529002062345923578696109)
                  ·
                    refine ⟨5073375773379721342011041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13529002062345923578696109 5073375773379721342011041)
                    ·
                      refine ⟨3805031830034791006508281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5073375773379721342011041 3805031830034791006508281)
                      ·
                        rfl

theorem cell23_7410273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 1, 3, 1, 3, 2].length) (baseStart_7410273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7410273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7410273 prefixEnd_7410273 := by exact prefixLift 7410273
  have htrace : WordTrace (prefixWord ++ tailWord_7410273) baseStart_7410273 baseEnd_7410273 := by
    simpa [prefixWord, tailWord_7410273, baseEnd_7410273] using wordTrace_append hprefix tailTrace_7410273
  have hstable : (prefixWord ++ tailWord_7410273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7410273).length < 2 ^ (prefixWord ++ tailWord_7410273).sum := by decide
  have hdescent : baseEnd_7410273 < baseStart_7410273 := by decide
  rcases family_descends (prefixWord ++ tailWord_7410273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7410309 : List Nat := [1, 3, 1, 1, 4, 2, 2, 2, 7]
def baseStart_7410309 : Nat := 118140960795 + 7410309 * 2 ^ 59
def prefixEnd_7410309 : Nat := 4983230072969 + 3 ^ 40 * 7410309 * 2
def baseEnd_7410309 : Nat := 422783368370928096184235

theorem tailTrace_7410309 : CollatzResearch.WordTrace tailWord_7410309 prefixEnd_7410309 422783368370928096184235 := by
  unfold tailWord_7410309
  simp only [CollatzResearch.WordTrace]
  refine ⟨270276173310723547864337981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180184115540482365242891987 270276173310723547864337981)
  ·
    refine ⟨101353564991521330449126743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 270276173310723547864337981 101353564991521330449126743)
    ·
      refine ⟨152030347487281995673690115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101353564991521330449126743 152030347487281995673690115)
      ·
        refine ⟨228045521230922993510535173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152030347487281995673690115 228045521230922993510535173)
        ·
          refine ⟨42758535230798061283225345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 228045521230922993510535173 42758535230798061283225345)
          ·
            refine ⟨32068901423098545962419009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42758535230798061283225345 32068901423098545962419009)
            ·
              refine ⟨24051676067323909471814257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32068901423098545962419009 24051676067323909471814257)
              ·
                refine ⟨18038757050492932103860693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24051676067323909471814257 18038757050492932103860693)
                ·
                  refine ⟨422783368370928096184235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18038757050492932103860693 422783368370928096184235)
                  ·
                    rfl

theorem cell23_7410309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 2, 2, 7].length) (baseStart_7410309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7410309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7410309 prefixEnd_7410309 := by exact prefixLift 7410309
  have htrace : WordTrace (prefixWord ++ tailWord_7410309) baseStart_7410309 baseEnd_7410309 := by
    simpa [prefixWord, tailWord_7410309, baseEnd_7410309] using wordTrace_append hprefix tailTrace_7410309
  have hstable : (prefixWord ++ tailWord_7410309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7410309).length < 2 ^ (prefixWord ++ tailWord_7410309).sum := by decide
  have hdescent : baseEnd_7410309 < baseStart_7410309 := by decide
  rcases family_descends (prefixWord ++ tailWord_7410309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7410376 : List Nat := [2, 1, 3, 1, 2, 3, 1, 3, 2, 1, 4]
def baseStart_7410376 : Nat := 118140960795 + 7410376 * 2 ^ 59
def prefixEnd_7410376 : Nat := 4983230072969 + 3 ^ 40 * 7410376 * 2
def baseEnd_7410376 : Nat := 3805084718542204103520307

theorem tailTrace_7410376 : CollatzResearch.WordTrace tailWord_7410376 prefixEnd_7410376 3805084718542204103520307 := by
  unfold tailWord_7410376
  simp only [CollatzResearch.WordTrace]
  refine ⟨135139308500740409153513491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180185744667653878871351321 135139308500740409153513491)
  ·
    refine ⟨202708962751110613730270237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135139308500740409153513491 202708962751110613730270237)
    ·
      refine ⟨76015861031666480148851339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 202708962751110613730270237 76015861031666480148851339)
      ·
        refine ⟨114023791547499720223277009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76015861031666480148851339 114023791547499720223277009)
        ·
          refine ⟨85517843660624790167457757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114023791547499720223277009 85517843660624790167457757)
          ·
            refine ⟨32069191372734296312796659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 85517843660624790167457757 32069191372734296312796659)
            ·
              refine ⟨48103787059101444469194989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32069191372734296312796659 48103787059101444469194989)
              ·
                refine ⟨18038920147163041675948121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48103787059101444469194989 18038920147163041675948121)
                ·
                  refine ⟨13529190110372281256961091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18038920147163041675948121 13529190110372281256961091)
                  ·
                    refine ⟨20293785165558421885441637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13529190110372281256961091 20293785165558421885441637)
                    ·
                      refine ⟨3805084718542204103520307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20293785165558421885441637 3805084718542204103520307)
                      ·
                        rfl

theorem cell23_7410376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 1, 3, 2, 1, 4].length) (baseStart_7410376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7410376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7410376 prefixEnd_7410376 := by exact prefixLift 7410376
  have htrace : WordTrace (prefixWord ++ tailWord_7410376) baseStart_7410376 baseEnd_7410376 := by
    simpa [prefixWord, tailWord_7410376, baseEnd_7410376] using wordTrace_append hprefix tailTrace_7410376
  have hstable : (prefixWord ++ tailWord_7410376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7410376).length < 2 ^ (prefixWord ++ tailWord_7410376).sum := by decide
  have hdescent : baseEnd_7410376 < baseStart_7410376 := by decide
  rcases family_descends (prefixWord ++ tailWord_7410376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7410430 : List Nat := [4, 2, 2, 1, 2, 1, 3, 1, 2, 2, 3]
def baseStart_7410430 : Nat := 118140960795 + 7410430 * 2 ^ 59
def prefixEnd_7410430 : Nat := 4983230072969 + 3 ^ 40 * 7410430 * 2
def baseEnd_7410430 : Nat := 3805112446497546892245059

theorem tailTrace_7410430 : CollatzResearch.WordTrace tailWord_7410430 prefixEnd_7410430 3805112446497546892245059 := by
  unfold tailWord_7410430
  simp only [CollatzResearch.WordTrace]
  refine ⟨33785073317910648191186593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 180187057695523457019661829 33785073317910648191186593)
  ·
    refine ⟨25338804988432986143389945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33785073317910648191186593 25338804988432986143389945)
    ·
      refine ⟨19004103741324739607542459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25338804988432986143389945 19004103741324739607542459)
      ·
        refine ⟨28506155611987109411313689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19004103741324739607542459 28506155611987109411313689)
        ·
          refine ⟨21379616708990332058485267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28506155611987109411313689 21379616708990332058485267)
          ·
            refine ⟨32069425063485498087727901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21379616708990332058485267 32069425063485498087727901)
            ·
              refine ⟨12026034398807061782897963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32069425063485498087727901 12026034398807061782897963)
              ·
                refine ⟨18039051598210592674346945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12026034398807061782897963 18039051598210592674346945)
                ·
                  refine ⟨13529288698657944505760209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18039051598210592674346945 13529288698657944505760209)
                  ·
                    refine ⟨10146966523993458379320157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13529288698657944505760209 10146966523993458379320157)
                    ·
                      refine ⟨3805112446497546892245059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10146966523993458379320157 3805112446497546892245059)
                      ·
                        rfl

theorem cell23_7410430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 3, 1, 2, 2, 3].length) (baseStart_7410430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7410430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7410430 prefixEnd_7410430 := by exact prefixLift 7410430
  have htrace : WordTrace (prefixWord ++ tailWord_7410430) baseStart_7410430 baseEnd_7410430 := by
    simpa [prefixWord, tailWord_7410430, baseEnd_7410430] using wordTrace_append hprefix tailTrace_7410430
  have hstable : (prefixWord ++ tailWord_7410430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7410430).length < 2 ^ (prefixWord ++ tailWord_7410430).sum := by decide
  have hdescent : baseEnd_7410430 < baseStart_7410430 := by decide
  rcases family_descends (prefixWord ++ tailWord_7410430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7410453 : List Nat := [1, 3, 2, 1, 2, 2, 2, 1, 4, 3, 2]
def baseStart_7410453 : Nat := 118140960795 + 7410453 * 2 ^ 59
def prefixEnd_7410453 : Nat := 4983230072969 + 3 ^ 40 * 7410453 * 2
def baseEnd_7410453 : Nat := 3805124256552600302257453

theorem tailTrace_7410453 : CollatzResearch.WordTrace tailWord_7410453 prefixEnd_7410453 3805124256552600302257453 := by
  unfold tailWord_7410453
  simp only [CollatzResearch.WordTrace]
  refine ⟨270281425422201860457580013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180187616948134573638386675 270281425422201860457580013)
  ·
    refine ⟨101355534533325697671592505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 270281425422201860457580013 101355534533325697671592505)
    ·
      refine ⟨76016650899994273253694379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101355534533325697671592505 76016650899994273253694379)
      ·
        refine ⟨114024976349991409880541569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76016650899994273253694379 114024976349991409880541569)
        ·
          refine ⟨85518732262493557410406177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114024976349991409880541569 85518732262493557410406177)
          ·
            refine ⟨64139049196870168057804633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85518732262493557410406177 64139049196870168057804633)
            ·
              refine ⟨48104286897652626043353475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64139049196870168057804633 48104286897652626043353475)
              ·
                refine ⟨72156430346478939065030213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48104286897652626043353475 72156430346478939065030213)
                ·
                  refine ⟨13529330689964801074693165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 72156430346478939065030213 13529330689964801074693165)
                  ·
                    refine ⟨5073499008736800403009937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13529330689964801074693165 5073499008736800403009937)
                    ·
                      refine ⟨3805124256552600302257453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5073499008736800403009937 3805124256552600302257453)
                      ·
                        rfl

theorem cell23_7410453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 2, 1, 4, 3, 2].length) (baseStart_7410453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7410453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7410453 prefixEnd_7410453 := by exact prefixLift 7410453
  have htrace : WordTrace (prefixWord ++ tailWord_7410453) baseStart_7410453 baseEnd_7410453 := by
    simpa [prefixWord, tailWord_7410453, baseEnd_7410453] using wordTrace_append hprefix tailTrace_7410453
  have hstable : (prefixWord ++ tailWord_7410453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7410453).length < 2 ^ (prefixWord ++ tailWord_7410453).sum := by decide
  have hdescent : baseEnd_7410453 < baseStart_7410453 := by decide
  rcases family_descends (prefixWord ++ tailWord_7410453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7410460 : List Nat := [2, 2, 3, 1, 1, 4, 2, 1, 3, 1, 3]
def baseStart_7410460 : Nat := 118140960795 + 7410460 * 2 ^ 59
def prefixEnd_7410460 : Nat := 4983230072969 + 3 ^ 40 * 7410460 * 2
def baseEnd_7410460 : Nat := 3805127850917181774869921

theorem tailTrace_7410460 : CollatzResearch.WordTrace tailWord_7410460 prefixEnd_7410460 3805127850917181774869921 := by
  unfold tailWord_7410460
  simp only [CollatzResearch.WordTrace]
  refine ⟨135140840366588250326542417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180187787155451000435389889 135140840366588250326542417)
  ·
    refine ⟨101355630274941187744906813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135140840366588250326542417 101355630274941187744906813)
    ·
      refine ⟨38008361353102945404340055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 101355630274941187744906813 38008361353102945404340055)
      ·
        refine ⟨57012542029654418106510083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38008361353102945404340055 57012542029654418106510083)
        ·
          refine ⟨85518813044481627159765125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57012542029654418106510083 85518813044481627159765125)
          ·
            refine ⟨16034777445840305092455961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 85518813044481627159765125 16034777445840305092455961)
            ·
              refine ⟨12026083084380228819341971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16034777445840305092455961 12026083084380228819341971)
              ·
                refine ⟨18039124626570343229012957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12026083084380228819341971 18039124626570343229012957)
                ·
                  refine ⟨6764671734963878710879859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18039124626570343229012957 6764671734963878710879859)
                  ·
                    refine ⟨10147007602445818066319789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6764671734963878710879859 10147007602445818066319789)
                    ·
                      refine ⟨3805127850917181774869921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10147007602445818066319789 3805127850917181774869921)
                      ·
                        rfl

theorem cell23_7410460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 2, 1, 3, 1, 3].length) (baseStart_7410460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7410460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7410460 prefixEnd_7410460 := by exact prefixLift 7410460
  have htrace : WordTrace (prefixWord ++ tailWord_7410460) baseStart_7410460 baseEnd_7410460 := by
    simpa [prefixWord, tailWord_7410460, baseEnd_7410460] using wordTrace_append hprefix tailTrace_7410460
  have hstable : (prefixWord ++ tailWord_7410460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7410460).length < 2 ^ (prefixWord ++ tailWord_7410460).sum := by decide
  have hdescent : baseEnd_7410460 < baseStart_7410460 := by decide
  rcases family_descends (prefixWord ++ tailWord_7410460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7410483 : List Nat := [1, 1, 1, 2, 6, 1, 1, 4, 1, 1, 4]
def baseStart_7410483 : Nat := 118140960795 + 7410483 * 2 ^ 59
def prefixEnd_7410483 : Nat := 4983230072969 + 3 ^ 40 * 7410483 * 2
def baseEnd_7410483 : Nat := 3805139660972235184882315

theorem tailTrace_7410483 : CollatzResearch.WordTrace tailWord_7410483 prefixEnd_7410483 3805139660972235184882315 := by
  unfold tailWord_7410483
  simp only [CollatzResearch.WordTrace]
  refine ⟨270282519612093175581172103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180188346408062117054114735 270282519612093175581172103)
  ·
    refine ⟨405423779418139763371758155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270282519612093175581172103 405423779418139763371758155)
    ·
      refine ⟨608135669127209645057637233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 405423779418139763371758155 608135669127209645057637233)
      ·
        refine ⟨456101751845407233793227925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 608135669127209645057637233 456101751845407233793227925)
        ·
          refine ⟨21379769617753464084057559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 456101751845407233793227925 21379769617753464084057559)
          ·
            refine ⟨32069654426630196126086339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21379769617753464084057559 32069654426630196126086339)
            ·
              refine ⟨48104481639945294189129509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32069654426630196126086339 48104481639945294189129509)
              ·
                refine ⟨9019590307489742660461783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48104481639945294189129509 9019590307489742660461783)
                ·
                  refine ⟨13529385461234613990692675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9019590307489742660461783 13529385461234613990692675)
                  ·
                    refine ⟨20294078191851920986039013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13529385461234613990692675 20294078191851920986039013)
                    ·
                      refine ⟨3805139660972235184882315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20294078191851920986039013 3805139660972235184882315)
                      ·
                        rfl

theorem cell23_7410483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 1, 4, 1, 1, 4].length) (baseStart_7410483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7410483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7410483 prefixEnd_7410483 := by exact prefixLift 7410483
  have htrace : WordTrace (prefixWord ++ tailWord_7410483) baseStart_7410483 baseEnd_7410483 := by
    simpa [prefixWord, tailWord_7410483, baseEnd_7410483] using wordTrace_append hprefix tailTrace_7410483
  have hstable : (prefixWord ++ tailWord_7410483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7410483).length < 2 ^ (prefixWord ++ tailWord_7410483).sum := by decide
  have hdescent : baseEnd_7410483 < baseStart_7410483 := by decide
  rcases family_descends (prefixWord ++ tailWord_7410483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7410496 : List Nat := [2, 1, 1, 2, 2, 1, 1, 6, 1, 2, 4]
def baseStart_7410496 : Nat := 118140960795 + 7410496 * 2 ^ 59
def prefixEnd_7410496 : Nat := 4983230072969 + 3 ^ 40 * 7410496 * 2
def baseEnd_7410496 : Nat := 3805146336220743634019755

theorem tailTrace_7410496 : CollatzResearch.WordTrace tailWord_7410496 prefixEnd_7410496 3805146336220743634019755 := by
  unfold tailWord_7410496
  simp only [CollatzResearch.WordTrace]
  refine ⟨135141496880523039400697671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180188662507364052534263561 135141496880523039400697671)
  ·
    refine ⟨202712245320784559101046507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135141496880523039400697671 202712245320784559101046507)
    ·
      refine ⟨304068367981176838651569761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202712245320784559101046507 304068367981176838651569761)
      ·
        refine ⟨228051275985882628988677321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 304068367981176838651569761 228051275985882628988677321)
        ·
          refine ⟨171038456989411971741507991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 228051275985882628988677321 171038456989411971741507991)
          ·
            refine ⟨256557685484117957612261987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 171038456989411971741507991 256557685484117957612261987)
            ·
              refine ⟨384836528226176936418392981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 256557685484117957612261987 384836528226176936418392981)
              ·
                refine ⟨18039212260602043894612171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 384836528226176936418392981 18039212260602043894612171)
                ·
                  refine ⟨27058818390903065841918257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18039212260602043894612171 27058818390903065841918257)
                  ·
                    refine ⟨20294113793177299381438693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27058818390903065841918257 20294113793177299381438693)
                    ·
                      refine ⟨3805146336220743634019755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20294113793177299381438693 3805146336220743634019755)
                      ·
                        rfl

theorem cell23_7410496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 6, 1, 2, 4].length) (baseStart_7410496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7410496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7410496 prefixEnd_7410496 := by exact prefixLift 7410496
  have htrace : WordTrace (prefixWord ++ tailWord_7410496) baseStart_7410496 baseEnd_7410496 := by
    simpa [prefixWord, tailWord_7410496, baseEnd_7410496] using wordTrace_append hprefix tailTrace_7410496
  have hstable : (prefixWord ++ tailWord_7410496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7410496).length < 2 ^ (prefixWord ++ tailWord_7410496).sum := by decide
  have hdescent : baseEnd_7410496 < baseStart_7410496 := by decide
  rcases family_descends (prefixWord ++ tailWord_7410496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7410546 : List Nat := [3, 2, 1, 2, 1, 1, 2, 1, 1, 4, 5]
def baseStart_7410546 : Nat := 118140960795 + 7410546 * 2 ^ 59
def prefixEnd_7410546 : Nat := 4983230072969 + 3 ^ 40 * 7410546 * 2
def baseEnd_7410546 : Nat := 3805172010253468438394525

theorem tailTrace_7410546 : CollatzResearch.WordTrace tailWord_7410546 prefixEnd_7410546 3805172010253468438394525 := by
  unfold tailWord_7410546
  simp only [CollatzResearch.WordTrace]
  refine ⟨67571204352716234335178873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 180189878273909958227143661 67571204352716234335178873)
  ·
    refine ⟨50678403264537175751384155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67571204352716234335178873 50678403264537175751384155)
    ·
      refine ⟨76017604896805763627076233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50678403264537175751384155 76017604896805763627076233)
      ·
        refine ⟨57013203672604322720307175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76017604896805763627076233 57013203672604322720307175)
        ·
          refine ⟨85519805508906484080460763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57013203672604322720307175 85519805508906484080460763)
          ·
            refine ⟨128279708263359726120691145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85519805508906484080460763 128279708263359726120691145)
            ·
              refine ⟨96209781197519794590518359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 128279708263359726120691145 96209781197519794590518359)
              ·
                refine ⟨144314671796279691885777539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 96209781197519794590518359 144314671796279691885777539)
                ·
                  refine ⟨216472007694419537828666309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 144314671796279691885777539 216472007694419537828666309)
                  ·
                    refine ⟨40588501442703663342874933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 216472007694419537828666309 40588501442703663342874933)
                    ·
                      refine ⟨3805172010253468438394525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40588501442703663342874933 3805172010253468438394525)
                      ·
                        rfl

theorem cell23_7410546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 1, 1, 4, 5].length) (baseStart_7410546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7410546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7410546 prefixEnd_7410546 := by exact prefixLift 7410546
  have htrace : WordTrace (prefixWord ++ tailWord_7410546) baseStart_7410546 baseEnd_7410546 := by
    simpa [prefixWord, tailWord_7410546, baseEnd_7410546] using wordTrace_append hprefix tailTrace_7410546
  have hstable : (prefixWord ++ tailWord_7410546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7410546).length < 2 ^ (prefixWord ++ tailWord_7410546).sum := by decide
  have hdescent : baseEnd_7410546 < baseStart_7410546 := by decide
  rcases family_descends (prefixWord ++ tailWord_7410546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7410550 : List Nat := [5, 1, 1, 3, 1, 1, 1, 1, 3, 3, 3]
def baseStart_7410550 : Nat := 118140960795 + 7410550 * 2 ^ 59
def prefixEnd_7410550 : Nat := 4983230072969 + 3 ^ 40 * 7410550 * 2
def baseEnd_7410550 : Nat := 3805174064176086422744507

theorem tailTrace_7410550 : CollatzResearch.WordTrace tailWord_7410550 prefixEnd_7410550 3805174064176086422744507 := by
  unfold tailWord_7410550
  simp only [CollatzResearch.WordTrace]
  refine ⟨16892810206428152876491319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 180189975535233630682574069 16892810206428152876491319)
  ·
    refine ⟨25339215309642229314736979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16892810206428152876491319 25339215309642229314736979)
    ·
      refine ⟨38008822964463343972105469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25339215309642229314736979 38008822964463343972105469)
      ·
        refine ⟨14253308611673753989539551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38008822964463343972105469 14253308611673753989539551)
        ·
          refine ⟨21379962917510630984309327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14253308611673753989539551 21379962917510630984309327)
          ·
            refine ⟨32069944376265946476463991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21379962917510630984309327 32069944376265946476463991)
            ·
              refine ⟨48104916564398919714695987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32069944376265946476463991 48104916564398919714695987)
              ·
                refine ⟨72157374846598379572043981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48104916564398919714695987 72157374846598379572043981)
                ·
                  refine ⟨27059015567474392339516493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 72157374846598379572043981 27059015567474392339516493)
                  ·
                    refine ⟨10147130837802897127318685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27059015567474392339516493 10147130837802897127318685)
                    ·
                      refine ⟨3805174064176086422744507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10147130837802897127318685 3805174064176086422744507)
                      ·
                        rfl

theorem cell23_7410550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 1, 1, 3, 3, 3].length) (baseStart_7410550 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7410550 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7410550 prefixEnd_7410550 := by exact prefixLift 7410550
  have htrace : WordTrace (prefixWord ++ tailWord_7410550) baseStart_7410550 baseEnd_7410550 := by
    simpa [prefixWord, tailWord_7410550, baseEnd_7410550] using wordTrace_append hprefix tailTrace_7410550
  have hstable : (prefixWord ++ tailWord_7410550).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7410550).length < 2 ^ (prefixWord ++ tailWord_7410550).sum := by decide
  have hdescent : baseEnd_7410550 < baseStart_7410550 := by decide
  rcases family_descends (prefixWord ++ tailWord_7410550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7410556 : List Nat := [2, 2, 2, 1, 1, 1, 1, 2, 4, 3, 4]
def baseStart_7410556 : Nat := 118140960795 + 7410556 * 2 ^ 59
def prefixEnd_7410556 : Nat := 4983230072969 + 3 ^ 40 * 7410556 * 2
def baseEnd_7410556 : Nat := 3805177145060013399269479

theorem tailTrace_7410556 : CollatzResearch.WordTrace tailWord_7410556 prefixEnd_7410556 3805177145060013399269479 := by
  unfold tailWord_7410556
  simp only [CollatzResearch.WordTrace]
  refine ⟨135142591070414354524289761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180190121427219139365719681 135142591070414354524289761)
  ·
    refine ⟨101356943302810765893217321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135142591070414354524289761 101356943302810765893217321)
    ·
      refine ⟨76017707477108074419912991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101356943302810765893217321 76017707477108074419912991)
      ·
        refine ⟨114026561215662111629869487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76017707477108074419912991 114026561215662111629869487)
        ·
          refine ⟨171039841823493167444804231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114026561215662111629869487 171039841823493167444804231)
          ·
            refine ⟨256559762735239751167206347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 171039841823493167444804231 256559762735239751167206347)
            ·
              refine ⟨384839644102859626750809521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 256559762735239751167206347 384839644102859626750809521)
              ·
                refine ⟨288629733077144720063107141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 384839644102859626750809521 288629733077144720063107141)
                ·
                  refine ⟨54118074951964635011832589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 288629733077144720063107141 54118074951964635011832589)
                  ·
                    refine ⟨20294278106986738129437221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 54118074951964635011832589 20294278106986738129437221)
                    ·
                      refine ⟨3805177145060013399269479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20294278106986738129437221 3805177145060013399269479)
                      ·
                        rfl

theorem cell23_7410556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 2, 4, 3, 4].length) (baseStart_7410556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7410556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7410556 prefixEnd_7410556 := by exact prefixLift 7410556
  have htrace : WordTrace (prefixWord ++ tailWord_7410556) baseStart_7410556 baseEnd_7410556 := by
    simpa [prefixWord, tailWord_7410556, baseEnd_7410556] using wordTrace_append hprefix tailTrace_7410556
  have hstable : (prefixWord ++ tailWord_7410556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7410556).length < 2 ^ (prefixWord ++ tailWord_7410556).sum := by decide
  have hdescent : baseEnd_7410556 < baseStart_7410556 := by decide
  rcases family_descends (prefixWord ++ tailWord_7410556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7410567 : List Nat := [1, 1, 4, 2, 3, 2, 2, 2, 2, 1, 3]
def baseStart_7410567 : Nat := 118140960795 + 7410567 * 2 ^ 59
def prefixEnd_7410567 : Nat := 4983230072969 + 3 ^ 40 * 7410567 * 2
def baseEnd_7410567 : Nat := 3805182793347212856231929

theorem tailTrace_7410567 : CollatzResearch.WordTrace tailWord_7410567 prefixEnd_7410567 3805182793347212856231929 := by
  unfold tailWord_7410567
  simp only [CollatzResearch.WordTrace]
  refine ⟨270285583343788857927229955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180190388895859238618153303 270285583343788857927229955)
  ·
    refine ⟨405428375015683286890844933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270285583343788857927229955 405428375015683286890844933)
    ·
      refine ⟨76017820315440616292033425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 405428375015683286890844933 76017820315440616292033425)
      ·
        refine ⟨57013365236580462219025069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76017820315440616292033425 57013365236580462219025069)
        ·
          refine ⟨21380011963717673332134401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57013365236580462219025069 21380011963717673332134401)
          ·
            refine ⟨16035008972788254999100801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21380011963717673332134401 16035008972788254999100801)
            ·
              refine ⟨12026256729591191249325601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16035008972788254999100801 12026256729591191249325601)
              ·
                refine ⟨9019692547193393436994201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12026256729591191249325601 9019692547193393436994201)
                ·
                  refine ⟨6764769410395045077745651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9019692547193393436994201 6764769410395045077745651)
                  ·
                    refine ⟨10147154115592567616618477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6764769410395045077745651 10147154115592567616618477)
                    ·
                      refine ⟨3805182793347212856231929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10147154115592567616618477 3805182793347212856231929)
                      ·
                        rfl

theorem cell23_7410567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 2, 2, 2, 1, 3].length) (baseStart_7410567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7410567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7410567 prefixEnd_7410567 := by exact prefixLift 7410567
  have htrace : WordTrace (prefixWord ++ tailWord_7410567) baseStart_7410567 baseEnd_7410567 := by
    simpa [prefixWord, tailWord_7410567, baseEnd_7410567] using wordTrace_append hprefix tailTrace_7410567
  have hstable : (prefixWord ++ tailWord_7410567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7410567).length < 2 ^ (prefixWord ++ tailWord_7410567).sum := by decide
  have hdescent : baseEnd_7410567 < baseStart_7410567 := by decide
  rcases family_descends (prefixWord ++ tailWord_7410567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7410624 : List Nat := [2, 1, 1, 2, 3, 5, 1, 2, 2, 2, 2]
def baseStart_7410624 : Nat := 118140960795 + 7410624 * 2 ^ 59
def prefixEnd_7410624 : Nat := 4983230072969 + 3 ^ 40 * 7410624 * 2
def baseEnd_7410624 : Nat := 3805212061744519133219167

theorem tailTrace_7410624 : CollatzResearch.WordTrace tailWord_7410624 prefixEnd_7410624 3805212061744519133219167 := by
  unfold tailWord_7410624
  simp only [CollatzResearch.WordTrace]
  refine ⟨135143831152291178331027463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180191774869721571108036617 135143831152291178331027463)
  ·
    refine ⟨202715746728436767496541195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135143831152291178331027463 202715746728436767496541195)
    ·
      refine ⟨304073620092655151244811793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202715746728436767496541195 304073620092655151244811793)
      ·
        refine ⟨228055215069491363433608845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 304073620092655151244811793 228055215069491363433608845)
        ·
          refine ⟨85520705651059261287603317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 228055215069491363433608845 85520705651059261287603317)
          ·
            refine ⟨8017566154786805745712811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 85520705651059261287603317 8017566154786805745712811)
            ·
              refine ⟨12026349232180208618569217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8017566154786805745712811 12026349232180208618569217)
              ·
                refine ⟨9019761924135156463926913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12026349232180208618569217 9019761924135156463926913)
                ·
                  refine ⟨6764821443101367347945185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9019761924135156463926913 6764821443101367347945185)
                  ·
                    refine ⟨5073616082326025510958889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6764821443101367347945185 5073616082326025510958889)
                    ·
                      refine ⟨3805212061744519133219167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5073616082326025510958889 3805212061744519133219167)
                      ·
                        rfl

theorem cell23_7410624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 5, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 5, 1, 2, 2, 2, 2].length) (baseStart_7410624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7410624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7410624 prefixEnd_7410624 := by exact prefixLift 7410624
  have htrace : WordTrace (prefixWord ++ tailWord_7410624) baseStart_7410624 baseEnd_7410624 := by
    simpa [prefixWord, tailWord_7410624, baseEnd_7410624] using wordTrace_append hprefix tailTrace_7410624
  have hstable : (prefixWord ++ tailWord_7410624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7410624).length < 2 ^ (prefixWord ++ tailWord_7410624).sum := by decide
  have hdescent : baseEnd_7410624 < baseStart_7410624 := by decide
  rcases family_descends (prefixWord ++ tailWord_7410624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7410713 : List Nat := [1, 2, 1, 2, 1, 1, 4, 1, 2, 5, 3]
def baseStart_7410713 : Nat := 118140960795 + 7410713 * 2 ^ 59
def prefixEnd_7410713 : Nat := 4983230072969 + 3 ^ 40 * 7410713 * 2
def baseEnd_7410713 : Nat := 3805257761522769285006257

theorem tailTrace_7410713 : CollatzResearch.WordTrace tailWord_7410713 prefixEnd_7410713 3805257761522769285006257 := by
  unfold tailWord_7410713
  simp only [CollatzResearch.WordTrace]
  refine ⟨270290908401259924862044793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180193938934173283241363195 270290908401259924862044793)
  ·
    refine ⟨202718181300944943646533595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 270290908401259924862044793 202718181300944943646533595)
    ·
      refine ⟨304077271951417415469800393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202718181300944943646533595 304077271951417415469800393)
      ·
        refine ⟨228057953963563061602350295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 304077271951417415469800393 228057953963563061602350295)
        ·
          refine ⟨342086930945344592403525443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 228057953963563061602350295 342086930945344592403525443)
          ·
            refine ⟨513130396418016888605288165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 342086930945344592403525443 513130396418016888605288165)
            ·
              refine ⟨96211949328378166613491531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 513130396418016888605288165 96211949328378166613491531)
              ·
                refine ⟨144317923992567249920237297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 96211949328378166613491531 144317923992567249920237297)
                ·
                  refine ⟨108238442994425437440177973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 144317923992567249920237297 108238442994425437440177973)
                  ·
                    refine ⟨10147354030727384760016685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 108238442994425437440177973 10147354030727384760016685)
                    ·
                      refine ⟨3805257761522769285006257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10147354030727384760016685 3805257761522769285006257)
                      ·
                        rfl

theorem cell23_7410713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 1, 2, 5, 3].length) (baseStart_7410713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7410713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7410713 prefixEnd_7410713 := by exact prefixLift 7410713
  have htrace : WordTrace (prefixWord ++ tailWord_7410713) baseStart_7410713 baseEnd_7410713 := by
    simpa [prefixWord, tailWord_7410713, baseEnd_7410713] using wordTrace_append hprefix tailTrace_7410713
  have hstable : (prefixWord ++ tailWord_7410713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7410713).length < 2 ^ (prefixWord ++ tailWord_7410713).sum := by decide
  have hdescent : baseEnd_7410713 < baseStart_7410713 := by decide
  rcases family_descends (prefixWord ++ tailWord_7410713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7410780 : List Nat := [2, 2, 4, 1, 1, 1, 1, 4, 1, 6]
def baseStart_7410780 : Nat := 118140960795 + 7410780 * 2 ^ 59
def prefixEnd_7410780 : Nat := 4983230072969 + 3 ^ 40 * 7410780 * 2
def baseEnd_7410780 : Nat := 1268430721575540174289483

theorem tailTrace_7410780 : CollatzResearch.WordTrace tailWord_7410780 prefixEnd_7410780 1268430721575540174289483 := by
  unfold tailWord_7410780
  simp only [CollatzResearch.WordTrace]
  refine ⟨135146676046008597652366897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180195568061344796869822529 135146676046008597652366897)
  ·
    refine ⟨101360007034506448239275173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135146676046008597652366897 101360007034506448239275173)
    ·
      refine ⟨19005001318969959044864095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 101360007034506448239275173 19005001318969959044864095)
      ·
        refine ⟨28507501978454938567296143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19005001318969959044864095 28507501978454938567296143)
        ·
          refine ⟨42761252967682407850944215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28507501978454938567296143 42761252967682407850944215)
          ·
            refine ⟨64141879451523611776416323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42761252967682407850944215 64141879451523611776416323)
            ·
              refine ⟨96212819177285417664624485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64141879451523611776416323 96212819177285417664624485)
              ·
                refine ⟨18039903595741015812117091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 96212819177285417664624485 18039903595741015812117091)
                ·
                  refine ⟨27059855393611523718175637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18039903595741015812117091 27059855393611523718175637)
                  ·
                    refine ⟨1268430721575540174289483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27059855393611523718175637 1268430721575540174289483)
                    ·
                      rfl

theorem cell23_7410780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 4, 1, 6].length) (baseStart_7410780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7410780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7410780 prefixEnd_7410780 := by exact prefixLift 7410780
  have htrace : WordTrace (prefixWord ++ tailWord_7410780) baseStart_7410780 baseEnd_7410780 := by
    simpa [prefixWord, tailWord_7410780, baseEnd_7410780] using wordTrace_append hprefix tailTrace_7410780
  have hstable : (prefixWord ++ tailWord_7410780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7410780).length < 2 ^ (prefixWord ++ tailWord_7410780).sum := by decide
  have hdescent : baseEnd_7410780 < baseStart_7410780 := by decide
  rcases family_descends (prefixWord ++ tailWord_7410780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7410787 : List Nat := [1, 1, 1, 5, 1, 1, 1, 1, 7, 2, 2]
def baseStart_7410787 : Nat := 118140960795 + 7410787 * 2 ^ 59
def prefixEnd_7410787 : Nat := 4983230072969 + 3 ^ 40 * 7410787 * 2
def baseEnd_7410787 : Nat := 3805295759091201995480917

theorem tailTrace_7410787 : CollatzResearch.WordTrace tailWord_7410787 prefixEnd_7410787 3805295759091201995480917 := by
  unfold tailWord_7410787
  simp only [CollatzResearch.WordTrace]
  refine ⟨270293607402991835500238615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180195738268661223666825743 270293607402991835500238615)
  ·
    refine ⟨405440411104487753250357923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270293607402991835500238615 405440411104487753250357923)
    ·
      refine ⟨608160616656731629875536885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 405440411104487753250357923 608160616656731629875536885)
      ·
        refine ⟨57015057811568590300831583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 608160616656731629875536885 57015057811568590300831583)
        ·
          refine ⟨85522586717352885451247375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57015057811568590300831583 85522586717352885451247375)
          ·
            refine ⟨128283880076029328176871063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85522586717352885451247375 128283880076029328176871063)
            ·
              refine ⟨192425820114043992265306595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 128283880076029328176871063 192425820114043992265306595)
              ·
                refine ⟨288638730171065988397959893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 192425820114043992265306595 288638730171065988397959893)
                ·
                  refine ⟨6764970238384359103077185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 288638730171065988397959893 6764970238384359103077185)
                  ·
                    refine ⟨5073727678788269327307889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6764970238384359103077185 5073727678788269327307889)
                    ·
                      refine ⟨3805295759091201995480917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5073727678788269327307889 3805295759091201995480917)
                      ·
                        rfl

theorem cell23_7410787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 1, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 1, 7, 2, 2].length) (baseStart_7410787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7410787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7410787 prefixEnd_7410787 := by exact prefixLift 7410787
  have htrace : WordTrace (prefixWord ++ tailWord_7410787) baseStart_7410787 baseEnd_7410787 := by
    simpa [prefixWord, tailWord_7410787, baseEnd_7410787] using wordTrace_append hprefix tailTrace_7410787
  have hstable : (prefixWord ++ tailWord_7410787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7410787).length < 2 ^ (prefixWord ++ tailWord_7410787).sum := by decide
  have hdescent : baseEnd_7410787 < baseStart_7410787 := by decide
  rcases family_descends (prefixWord ++ tailWord_7410787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7410793 : List Nat := [1, 2, 1, 1, 1, 7, 10]
def baseStart_7410793 : Nat := 118140960795 + 7410793 * 2 ^ 59
def prefixEnd_7410793 : Nat := 4983230072969 + 3 ^ 40 * 7410793 * 2
def baseEnd_7410793 : Nat := 46978998024384308296369

theorem tailTrace_7410793 : CollatzResearch.WordTrace tailWord_7410793 prefixEnd_7410793 46978998024384308296369 := by
  unfold tailWord_7410793
  simp only [CollatzResearch.WordTrace]
  refine ⟨270293826240970098524957033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180195884160646732349971355 270293826240970098524957033)
  ·
    refine ⟨202720369680727573893717775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 270293826240970098524957033 202720369680727573893717775)
    ·
      refine ⟨304080554521091360840576663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202720369680727573893717775 304080554521091360840576663)
      ·
        refine ⟨456120831781637041260864995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 304080554521091360840576663 456120831781637041260864995)
        ·
          refine ⟨684181247672455561891297493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 456120831781637041260864995 684181247672455561891297493)
          ·
            refine ⟨16035497992323177231827285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 684181247672455561891297493 16035497992323177231827285)
            ·
              refine ⟨46978998024384308296369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 16035497992323177231827285 46978998024384308296369)
              ·
                rfl

theorem cell23_7410793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 10].length) (baseStart_7410793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7410793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7410793 prefixEnd_7410793 := by exact prefixLift 7410793
  have htrace : WordTrace (prefixWord ++ tailWord_7410793) baseStart_7410793 baseEnd_7410793 := by
    simpa [prefixWord, tailWord_7410793, baseEnd_7410793] using wordTrace_append hprefix tailTrace_7410793
  have hstable : (prefixWord ++ tailWord_7410793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7410793).length < 2 ^ (prefixWord ++ tailWord_7410793).sum := by decide
  have hdescent : baseEnd_7410793 < baseStart_7410793 := by decide
  rcases family_descends (prefixWord ++ tailWord_7410793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7410797 : List Nat := [1, 5, 1, 1, 2, 3, 1, 1, 4, 4]
def baseStart_7410797 : Nat := 118140960795 + 7410797 * 2 ^ 59
def prefixEnd_7410797 : Nat := 4983230072969 + 3 ^ 40 * 7410797 * 2
def baseEnd_7410797 : Nat := 1268433631299248985451957

theorem tailTrace_7410797 : CollatzResearch.WordTrace tailWord_7410797 prefixEnd_7410797 1268433631299248985451957 := by
  unfold tailWord_7410797
  simp only [CollatzResearch.WordTrace]
  refine ⟨270293972132955607208102645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180195981421970404805401763 270293972132955607208102645)
  ·
    refine ⟨25340059887464588175759623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 270293972132955607208102645 25340059887464588175759623)
    ·
      refine ⟨38010089831196882263639435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25340059887464588175759623 38010089831196882263639435)
      ·
        refine ⟨57015134746795323395459153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38010089831196882263639435 57015134746795323395459153)
        ·
          refine ⟨42761351060096492546594365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57015134746795323395459153 42761351060096492546594365)
          ·
            refine ⟨16035506647536184704972887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42761351060096492546594365 16035506647536184704972887)
            ·
              refine ⟨24053259971304277057459331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16035506647536184704972887 24053259971304277057459331)
              ·
                refine ⟨36079889956956415586188997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24053259971304277057459331 36079889956956415586188997)
                ·
                  refine ⟨6764979366929327922410437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36079889956956415586188997 6764979366929327922410437)
                  ·
                    refine ⟨1268433631299248985451957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6764979366929327922410437 1268433631299248985451957)
                    ·
                      rfl

theorem cell23_7410797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 1, 1, 4, 4].length) (baseStart_7410797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7410797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7410797 prefixEnd_7410797 := by exact prefixLift 7410797
  have htrace : WordTrace (prefixWord ++ tailWord_7410797) baseStart_7410797 baseEnd_7410797 := by
    simpa [prefixWord, tailWord_7410797, baseEnd_7410797] using wordTrace_append hprefix tailTrace_7410797
  have hstable : (prefixWord ++ tailWord_7410797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7410797).length < 2 ^ (prefixWord ++ tailWord_7410797).sum := by decide
  have hdescent : baseEnd_7410797 < baseStart_7410797 := by decide
  rcases family_descends (prefixWord ++ tailWord_7410797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7410817 : List Nat := [1, 2, 4, 2, 2, 1, 3, 1, 1, 2, 4]
def baseStart_7410817 : Nat := 118140960795 + 7410817 * 2 ^ 59
def prefixEnd_7410817 : Nat := 4983230072969 + 3 ^ 40 * 7410817 * 2
def baseEnd_7410817 : Nat := 3805311163510836878105779

theorem tailTrace_7410817 : CollatzResearch.WordTrace tailWord_7410817 prefixEnd_7410817 3805311163510836878105779 := by
  unfold tailWord_7410817
  simp only [CollatzResearch.WordTrace]
  refine ⟨270294701592883150623830705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180196467728588767082553803 270294701592883150623830705)
  ·
    refine ⟨202721026194662362967873029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 270294701592883150623830705 202721026194662362967873029)
    ·
      refine ⟨38010192411499193056476193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 202721026194662362967873029 38010192411499193056476193)
      ·
        refine ⟨28507644308624394792357145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38010192411499193056476193 28507644308624394792357145)
        ·
          refine ⟨21380733231468296094267859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28507644308624394792357145 21380733231468296094267859)
          ·
            refine ⟨32071099847202444141401789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21380733231468296094267859 32071099847202444141401789)
            ·
              refine ⟨12026662442700916553025671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32071099847202444141401789 12026662442700916553025671)
              ·
                refine ⟨18039993664051374829538507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12026662442700916553025671 18039993664051374829538507)
                ·
                  refine ⟨27059990496077062244307761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18039993664051374829538507 27059990496077062244307761)
                  ·
                    refine ⟨20294992872057796683230821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27059990496077062244307761 20294992872057796683230821)
                    ·
                      refine ⟨3805311163510836878105779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20294992872057796683230821 3805311163510836878105779)
                      ·
                        rfl

theorem cell23_7410817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 3, 1, 1, 2, 4].length) (baseStart_7410817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7410817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7410817 prefixEnd_7410817 := by exact prefixLift 7410817
  have htrace : WordTrace (prefixWord ++ tailWord_7410817) baseStart_7410817 baseEnd_7410817 := by
    simpa [prefixWord, tailWord_7410817, baseEnd_7410817] using wordTrace_append hprefix tailTrace_7410817
  have hstable : (prefixWord ++ tailWord_7410817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7410817).length < 2 ^ (prefixWord ++ tailWord_7410817).sum := by decide
  have hdescent : baseEnd_7410817 < baseStart_7410817 := by decide
  rcases family_descends (prefixWord ++ tailWord_7410817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7410855 : List Nat := [1, 1, 6, 2, 1, 2, 3, 2, 1, 2, 2]
def baseStart_7410855 : Nat := 118140960795 + 7410855 * 2 ^ 59
def prefixEnd_7410855 : Nat := 4983230072969 + 3 ^ 40 * 7410855 * 2
def baseEnd_7410855 : Nat := 3805330675775707729430605

theorem tailTrace_7410855 : CollatzResearch.WordTrace tailWord_7410855 prefixEnd_7410855 3805330675775707729430605 := by
  unfold tailWord_7410855
  simp only [CollatzResearch.WordTrace]
  refine ⟨270296087566745483113714019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180197391711163655409142679 270296087566745483113714019)
  ·
    refine ⟨405444131350118224670571029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270296087566745483113714019 405444131350118224670571029)
    ·
      refine ⟨19005193657036791781433017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 405444131350118224670571029 19005193657036791781433017)
      ·
        refine ⟨14253895242777593836074763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19005193657036791781433017 14253895242777593836074763)
        ·
          refine ⟨21380842864166390754112145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14253895242777593836074763 21380842864166390754112145)
          ·
            refine ⟨16035632148124793065584109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21380842864166390754112145 16035632148124793065584109)
            ·
              refine ⟨6013362055546797399594041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16035632148124793065584109 6013362055546797399594041)
              ·
                refine ⟨4510021541660098049695531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6013362055546797399594041 4510021541660098049695531)
                ·
                  refine ⟨6765032312490147074543297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4510021541660098049695531 6765032312490147074543297)
                  ·
                    refine ⟨5073774234367610305907473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6765032312490147074543297 5073774234367610305907473)
                    ·
                      refine ⟨3805330675775707729430605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5073774234367610305907473 3805330675775707729430605)
                      ·
                        rfl

theorem cell23_7410855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 3, 2, 1, 2, 2].length) (baseStart_7410855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7410855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7410855 prefixEnd_7410855 := by exact prefixLift 7410855
  have htrace : WordTrace (prefixWord ++ tailWord_7410855) baseStart_7410855 baseEnd_7410855 := by
    simpa [prefixWord, tailWord_7410855, baseEnd_7410855] using wordTrace_append hprefix tailTrace_7410855
  have hstable : (prefixWord ++ tailWord_7410855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7410855).length < 2 ^ (prefixWord ++ tailWord_7410855).sum := by decide
  have hdescent : baseEnd_7410855 < baseStart_7410855 := by decide
  rcases family_descends (prefixWord ++ tailWord_7410855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7410881 : List Nat := [1, 2, 6, 1, 1, 2, 1, 1, 3, 3, 2]
def baseStart_7410881 : Nat := 118140960795 + 7410881 * 2 ^ 59
def prefixEnd_7410881 : Nat := 4983230072969 + 3 ^ 40 * 7410881 * 2
def baseEnd_7410881 : Nat := 3805344026272724627705485

theorem tailTrace_7410881 : CollatzResearch.WordTrace tailWord_7410881 prefixEnd_7410881 3805344026272724627705485 := by
  unfold tailWord_7410881
  simp only [CollatzResearch.WordTrace]
  refine ⟨270297035864651289554160497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180198023909767526369440331 270297035864651289554160497)
  ·
    refine ⟨202722776898488467165620373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 270297035864651289554160497 202722776898488467165620373)
    ·
      refine ⟨9502630167116646898388455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 202722776898488467165620373 9502630167116646898388455)
      ·
        refine ⟨14253945250674970347582683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9502630167116646898388455 14253945250674970347582683)
        ·
          refine ⟨21380917876012455521374025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14253945250674970347582683 21380917876012455521374025)
          ·
            refine ⟨16035688407009341641030519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21380917876012455521374025 16035688407009341641030519)
            ·
              refine ⟨24053532610514012461545779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16035688407009341641030519 24053532610514012461545779)
              ·
                refine ⟨36080298915771018692318669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24053532610514012461545779 36080298915771018692318669)
                ·
                  refine ⟨13530112093414132009619501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36080298915771018692318669 13530112093414132009619501)
                  ·
                    refine ⟨5073792035030299503607313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13530112093414132009619501 5073792035030299503607313)
                    ·
                      refine ⟨3805344026272724627705485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5073792035030299503607313 3805344026272724627705485)
                      ·
                        rfl

theorem cell23_7410881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 1, 1, 3, 3, 2].length) (baseStart_7410881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7410881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7410881 prefixEnd_7410881 := by exact prefixLift 7410881
  have htrace : WordTrace (prefixWord ++ tailWord_7410881) baseStart_7410881 baseEnd_7410881 := by
    simpa [prefixWord, tailWord_7410881, baseEnd_7410881] using wordTrace_append hprefix tailTrace_7410881
  have hstable : (prefixWord ++ tailWord_7410881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7410881).length < 2 ^ (prefixWord ++ tailWord_7410881).sum := by decide
  have hdescent : baseEnd_7410881 < baseStart_7410881 := by decide
  rcases family_descends (prefixWord ++ tailWord_7410881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7410937 : List Nat := [1, 2, 1, 3, 1, 1, 3, 2, 2, 5, 2]
def baseStart_7410937 : Nat := 118140960795 + 7410937 * 2 ^ 59
def prefixEnd_7410937 : Nat := 4983230072969 + 3 ^ 40 * 7410937 * 2
def baseEnd_7410937 : Nat := 3805372781189376408605227

theorem tailTrace_7410937 : CollatzResearch.WordTrace tailWord_7410937 prefixEnd_7410937 3805372781189376408605227 := by
  unfold tailWord_7410937
  simp only [CollatzResearch.WordTrace]
  refine ⟨270299078352448411118199065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180199385568298940745466043 270299078352448411118199065)
  ·
    refine ⟨202724308764336308338649299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 270299078352448411118199065 202724308764336308338649299)
    ·
      refine ⟨304086463146504462507973949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202724308764336308338649299 304086463146504462507973949)
      ·
        refine ⟨114032423679939173440490231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 304086463146504462507973949 114032423679939173440490231)
        ·
          refine ⟨171048635519908760160735347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114032423679939173440490231 171048635519908760160735347)
          ·
            refine ⟨256572953279863140241103021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 171048635519908760160735347 256572953279863140241103021)
            ·
              refine ⟨96214857479948677590413633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 256572953279863140241103021 96214857479948677590413633)
              ·
                refine ⟨72161143109961508192810225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 96214857479948677590413633 72161143109961508192810225)
                ·
                  refine ⟨54120857332471131144607669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 72161143109961508192810225 54120857332471131144607669)
                  ·
                    refine ⟨5073830374919168544806969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 54120857332471131144607669 5073830374919168544806969)
                    ·
                      refine ⟨3805372781189376408605227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5073830374919168544806969 3805372781189376408605227)
                      ·
                        rfl

theorem cell23_7410937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 2, 2, 5, 2].length) (baseStart_7410937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7410937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7410937 prefixEnd_7410937 := by exact prefixLift 7410937
  have htrace : WordTrace (prefixWord ++ tailWord_7410937) baseStart_7410937 baseEnd_7410937 := by
    simpa [prefixWord, tailWord_7410937, baseEnd_7410937] using wordTrace_append hprefix tailTrace_7410937
  have hstable : (prefixWord ++ tailWord_7410937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7410937).length < 2 ^ (prefixWord ++ tailWord_7410937).sum := by decide
  have hdescent : baseEnd_7410937 < baseStart_7410937 := by decide
  rcases family_descends (prefixWord ++ tailWord_7410937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7410947 : List Nat := [1, 1, 1, 3, 2, 4, 3, 1, 2, 5]
def baseStart_7410947 : Nat := 118140960795 + 7410947 * 2 ^ 59
def prefixEnd_7410947 : Nat := 4983230072969 + 3 ^ 40 * 7410947 * 2
def baseEnd_7410947 : Nat := 1268459305331973789826727

theorem tailTrace_7410947 : CollatzResearch.WordTrace tailWord_7410947 prefixEnd_7410947 1268459305331973789826727 := by
  unfold tailWord_7410947
  simp only [CollatzResearch.WordTrace]
  refine ⟨270299443082412182826063095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180199628721608121884042063 270299443082412182826063095)
  ·
    refine ⟨405449164623618274239094643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270299443082412182826063095 405449164623618274239094643)
    ·
      refine ⟨608173746935427411358641965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 405449164623618274239094643 608173746935427411358641965)
      ·
        refine ⟨228065155100785279259490737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 608173746935427411358641965 228065155100785279259490737)
        ·
          refine ⟨171048866325588959444618053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 228065155100785279259490737 171048866325588959444618053)
          ·
            refine ⟨32071662436047929895865885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 171048866325588959444618053 32071662436047929895865885)
            ·
              refine ⟨12026873413517973710949707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32071662436047929895865885 12026873413517973710949707)
              ·
                refine ⟨18040310120276960566424561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12026873413517973710949707 18040310120276960566424561)
                ·
                  refine ⟨13530232590207720424818421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18040310120276960566424561 13530232590207720424818421)
                  ·
                    refine ⟨1268459305331973789826727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13530232590207720424818421 1268459305331973789826727)
                    ·
                      rfl

theorem cell23_7410947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 3, 1, 2, 5].length) (baseStart_7410947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7410947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7410947 prefixEnd_7410947 := by exact prefixLift 7410947
  have htrace : WordTrace (prefixWord ++ tailWord_7410947) baseStart_7410947 baseEnd_7410947 := by
    simpa [prefixWord, tailWord_7410947, baseEnd_7410947] using wordTrace_append hprefix tailTrace_7410947
  have hstable : (prefixWord ++ tailWord_7410947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7410947).length < 2 ^ (prefixWord ++ tailWord_7410947).sum := by decide
  have hdescent : baseEnd_7410947 < baseStart_7410947 := by decide
  rcases family_descends (prefixWord ++ tailWord_7410947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7410962 : List Nat := [3, 2, 4, 2, 1, 2, 1, 2, 2, 2, 2]
def baseStart_7410962 : Nat := 118140960795 + 7410962 * 2 ^ 59
def prefixEnd_7410962 : Nat := 4983230072969 + 3 ^ 40 * 7410962 * 2
def baseEnd_7410962 : Nat := 3805385618205738810792613

theorem tailTrace_7410962 : CollatzResearch.WordTrace tailWord_7410962 prefixEnd_7410962 3805385618205738810792613 := by
  unfold tailWord_7410962
  simp only [CollatzResearch.WordTrace]
  refine ⟨67574997544339460096964785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 180199993451571893591906093 67574997544339460096964785)
  ·
    refine ⟨50681248158254595072723589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67574997544339460096964785 50681248158254595072723589)
    ·
      refine ⟨9502734029672736576135673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 50681248158254595072723589 9502734029672736576135673)
      ·
        refine ⟨7127050522254552432101755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9502734029672736576135673 7127050522254552432101755)
        ·
          refine ⟨10690575783381828648152633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7127050522254552432101755 10690575783381828648152633)
          ·
            refine ⟨8017931837536371486114475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10690575783381828648152633 8017931837536371486114475)
            ·
              refine ⟨12026897756304557229171713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8017931837536371486114475 12026897756304557229171713)
              ·
                refine ⟨9020173317228417921878785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12026897756304557229171713 9020173317228417921878785)
                ·
                  refine ⟨6765129987921313441409089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9020173317228417921878785 6765129987921313441409089)
                  ·
                    refine ⟨5073847490940985081056817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6765129987921313441409089 5073847490940985081056817)
                    ·
                      refine ⟨3805385618205738810792613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5073847490940985081056817 3805385618205738810792613)
                      ·
                        rfl

theorem cell23_7410962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 2, 1, 2, 2, 2, 2].length) (baseStart_7410962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7410962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7410962 prefixEnd_7410962 := by exact prefixLift 7410962
  have htrace : WordTrace (prefixWord ++ tailWord_7410962) baseStart_7410962 baseEnd_7410962 := by
    simpa [prefixWord, tailWord_7410962, baseEnd_7410962] using wordTrace_append hprefix tailTrace_7410962
  have hstable : (prefixWord ++ tailWord_7410962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7410962).length < 2 ^ (prefixWord ++ tailWord_7410962).sum := by decide
  have hdescent : baseEnd_7410962 < baseStart_7410962 := by decide
  rcases family_descends (prefixWord ++ tailWord_7410962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7410967 : List Nat := [1, 1, 3, 4, 1, 1, 2, 1, 4, 1, 4]
def baseStart_7410967 : Nat := 118140960795 + 7410967 * 2 ^ 59
def prefixEnd_7410967 : Nat := 4983230072969 + 3 ^ 40 * 7410967 * 2
def baseEnd_7410967 : Nat := 3805388185609011291230089

theorem tailTrace_7410967 : CollatzResearch.WordTrace tailWord_7410967 prefixEnd_7410967 3805388185609011291230089 := by
  unfold tailWord_7410967
  simp only [CollatzResearch.WordTrace]
  refine ⟨270300172542339726241791155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180200115028226484161194103 270300172542339726241791155)
  ·
    refine ⟨405450258813509589362686733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270300172542339726241791155 405450258813509589362686733)
    ·
      refine ⟨152043847055066096011007525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 405450258813509589362686733 152043847055066096011007525)
      ·
        refine ⟨28508221322824893002063911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 152043847055066096011007525 28508221322824893002063911)
        ·
          refine ⟨42762331984237339503095867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28508221322824893002063911 42762331984237339503095867)
          ·
            refine ⟨64143497976356009254643801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42762331984237339503095867 64143497976356009254643801)
            ·
              refine ⟨48107623482267006940982851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64143497976356009254643801 48107623482267006940982851)
              ·
                refine ⟨72161435223400510411474277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48107623482267006940982851 72161435223400510411474277)
                ·
                  refine ⟨13530269104387595702151427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 72161435223400510411474277 13530269104387595702151427)
                  ·
                    refine ⟨20295403656581393553227141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13530269104387595702151427 20295403656581393553227141)
                    ·
                      refine ⟨3805388185609011291230089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20295403656581393553227141 3805388185609011291230089)
                      ·
                        rfl

theorem cell23_7410967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 2, 1, 4, 1, 4].length) (baseStart_7410967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7410967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7410967 prefixEnd_7410967 := by exact prefixLift 7410967
  have htrace : WordTrace (prefixWord ++ tailWord_7410967) baseStart_7410967 baseEnd_7410967 := by
    simpa [prefixWord, tailWord_7410967, baseEnd_7410967] using wordTrace_append hprefix tailTrace_7410967
  have hstable : (prefixWord ++ tailWord_7410967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7410967).length < 2 ^ (prefixWord ++ tailWord_7410967).sum := by decide
  have hdescent : baseEnd_7410967 < baseStart_7410967 := by decide
  rcases family_descends (prefixWord ++ tailWord_7410967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7410994 : List Nat := [3, 2, 1, 1, 4, 1, 2, 2, 3, 4]
def baseStart_7410994 : Nat := 118140960795 + 7410994 * 2 ^ 59
def prefixEnd_7410994 : Nat := 4983230072969 + 3 ^ 40 * 7410994 * 2
def baseEnd_7410994 : Nat := 1268467349862227561864155

theorem tailTrace_7410994 : CollatzResearch.WordTrace tailWord_7410994 prefixEnd_7410994 1268467349862227561864155 := by
  unfold tailWord_7410994
  simp only [CollatzResearch.WordTrace]
  refine ⟨67575289328310477463256009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 180200771542161273235349357 67575289328310477463256009)
  ·
    refine ⟨50681466996232858097442007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67575289328310477463256009 50681466996232858097442007)
    ·
      refine ⟨76022200494349287146163011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50681466996232858097442007 76022200494349287146163011)
      ·
        refine ⟨114033300741523930719244517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76022200494349287146163011 114033300741523930719244517)
        ·
          refine ⟨21381243889035737009858347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 114033300741523930719244517 21381243889035737009858347)
          ·
            refine ⟨32071865833553605514787521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21381243889035737009858347 32071865833553605514787521)
            ·
              refine ⟨24053899375165204136090641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32071865833553605514787521 24053899375165204136090641)
              ·
                refine ⟨18040424531373903102067981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24053899375165204136090641 18040424531373903102067981)
                ·
                  refine ⟨6765159199265213663275493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18040424531373903102067981 6765159199265213663275493)
                  ·
                    refine ⟨1268467349862227561864155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6765159199265213663275493 1268467349862227561864155)
                    ·
                      rfl

theorem cell23_7410994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 2, 2, 3, 4].length) (baseStart_7410994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7410994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7410994 prefixEnd_7410994 := by exact prefixLift 7410994
  have htrace : WordTrace (prefixWord ++ tailWord_7410994) baseStart_7410994 baseEnd_7410994 := by
    simpa [prefixWord, tailWord_7410994, baseEnd_7410994] using wordTrace_append hprefix tailTrace_7410994
  have hstable : (prefixWord ++ tailWord_7410994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7410994).length < 2 ^ (prefixWord ++ tailWord_7410994).sum := by decide
  have hdescent : baseEnd_7410994 < baseStart_7410994 := by decide
  rcases family_descends (prefixWord ++ tailWord_7410994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7411028 : List Nat := [2, 4, 1, 1, 2, 1, 5, 2, 1, 4]
def baseStart_7411028 : Nat := 118140960795 + 7411028 * 2 ^ 59
def prefixEnd_7411028 : Nat := 4983230072969 + 3 ^ 40 * 7411028 * 2
def baseEnd_7411028 : Nat := 1268473169309645184189103

theorem tailTrace_7411028 : CollatzResearch.WordTrace tailWord_7411028 prefixEnd_7411028 1268473169309645184189103 := by
  unfold tailWord_7411028
  simp only [CollatzResearch.WordTrace]
  refine ⟨135151198697559366829880869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180201598263412489106507825 135151198697559366829880869)
  ·
    refine ⟨25340849755792381280602663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 135151198697559366829880869 25340849755792381280602663)
    ·
      refine ⟨38011274633688571920903995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25340849755792381280602663 38011274633688571920903995)
      ·
        refine ⟨57016911950532857881355993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38011274633688571920903995 57016911950532857881355993)
        ·
          refine ⟨42762683962899643411016995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57016911950532857881355993 42762683962899643411016995)
          ·
            refine ⟨64144025944349465116525493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42762683962899643411016995 64144025944349465116525493)
            ·
              refine ⟨6013502432282762354674265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 64144025944349465116525493 6013502432282762354674265)
              ·
                refine ⟨4510126824212071766005699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6013502432282762354674265 4510126824212071766005699)
                ·
                  refine ⟨6765190236318107649008549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4510126824212071766005699 6765190236318107649008549)
                  ·
                    refine ⟨1268473169309645184189103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6765190236318107649008549 1268473169309645184189103)
                    ·
                      rfl

theorem cell23_7411028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 5, 2, 1, 4].length) (baseStart_7411028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7411028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7411028 prefixEnd_7411028 := by exact prefixLift 7411028
  have htrace : WordTrace (prefixWord ++ tailWord_7411028) baseStart_7411028 baseEnd_7411028 := by
    simpa [prefixWord, tailWord_7411028, baseEnd_7411028] using wordTrace_append hprefix tailTrace_7411028
  have hstable : (prefixWord ++ tailWord_7411028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7411028).length < 2 ^ (prefixWord ++ tailWord_7411028).sum := by decide
  have hdescent : baseEnd_7411028 < baseStart_7411028 := by decide
  rcases family_descends (prefixWord ++ tailWord_7411028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7411067 : List Nat := [1, 1, 1, 1, 1, 6, 3, 2, 1, 6]
def baseStart_7411067 : Nat := 118140960795 + 7411067 * 2 ^ 59
def prefixEnd_7411067 : Nat := 4983230072969 + 3 ^ 40 * 7411067 * 2
def baseEnd_7411067 : Nat := 1268479844558153633326543

theorem tailTrace_7411067 : CollatzResearch.WordTrace tailWord_7411067 prefixEnd_7411067 1268479844558153633326543 := by
  unfold tailWord_7411067
  simp only [CollatzResearch.WordTrace]
  refine ⟨270303819841977443320431455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180202546561318295546954303 270303819841977443320431455)
  ·
    refine ⟨405455729762966164980647183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270303819841977443320431455 405455729762966164980647183)
    ·
      refine ⟨608183594644449247470970775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 405455729762966164980647183 608183594644449247470970775)
      ·
        refine ⟨912275391966673871206456163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 608183594644449247470970775 912275391966673871206456163)
        ·
          refine ⟨1368413087950010806809684245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 912275391966673871206456163 1368413087950010806809684245)
          ·
            refine ⟨64144363497656756569203949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 1368413087950010806809684245 64144363497656756569203949)
            ·
              refine ⟨24054136311621283713451481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64144363497656756569203949 24054136311621283713451481)
              ·
                refine ⟨18040602233715962785088611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24054136311621283713451481 18040602233715962785088611)
                ·
                  refine ⟨27060903350573944177632917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18040602233715962785088611 27060903350573944177632917)
                  ·
                    refine ⟨1268479844558153633326543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27060903350573944177632917 1268479844558153633326543)
                    ·
                      rfl

theorem cell23_7411067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 3, 2, 1, 6].length) (baseStart_7411067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7411067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7411067 prefixEnd_7411067 := by exact prefixLift 7411067
  have htrace : WordTrace (prefixWord ++ tailWord_7411067) baseStart_7411067 baseEnd_7411067 := by
    simpa [prefixWord, tailWord_7411067, baseEnd_7411067] using wordTrace_append hprefix tailTrace_7411067
  have hstable : (prefixWord ++ tailWord_7411067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7411067).length < 2 ^ (prefixWord ++ tailWord_7411067).sum := by decide
  have hdescent : baseEnd_7411067 < baseStart_7411067 := by decide
  rcases family_descends (prefixWord ++ tailWord_7411067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7411097 : List Nat := [1, 2, 1, 2, 1, 5, 3, 8]
def baseStart_7411097 : Nat := 118140960795 + 7411097 * 2 ^ 59
def prefixEnd_7411097 : Nat := 4983230072969 + 3 ^ 40 * 7411097 * 2
def baseEnd_7411097 : Nat := 140942775484966510466833

theorem tailTrace_7411097 : CollatzResearch.WordTrace tailWord_7411097 prefixEnd_7411097 140942775484966510466833 := by
  unfold tailWord_7411097
  simp only [CollatzResearch.WordTrace]
  refine ⟨270304914031868758444023545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180203276021245838962682363 270304914031868758444023545)
  ·
    refine ⟨202728685523901568833017659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 270304914031868758444023545 202728685523901568833017659)
    ·
      refine ⟨304093028285852353249526489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202728685523901568833017659 304093028285852353249526489)
      ·
        refine ⟨228069771214389264937144867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 304093028285852353249526489 228069771214389264937144867)
        ·
          refine ⟨342104656821583897405717301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 228069771214389264937144867 342104656821583897405717301)
          ·
            refine ⟨32072311577023490381785997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 342104656821583897405717301 32072311577023490381785997)
            ·
              refine ⟨12027116841383808893169749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32072311577023490381785997 12027116841383808893169749)
              ·
                refine ⟨140942775484966510466833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12027116841383808893169749 140942775484966510466833)
                ·
                  rfl

theorem cell23_7411097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 3, 8].length) (baseStart_7411097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7411097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7411097 prefixEnd_7411097 := by exact prefixLift 7411097
  have htrace : WordTrace (prefixWord ++ tailWord_7411097) baseStart_7411097 baseEnd_7411097 := by
    simpa [prefixWord, tailWord_7411097, baseEnd_7411097] using wordTrace_append hprefix tailTrace_7411097
  have hstable : (prefixWord ++ tailWord_7411097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7411097).length < 2 ^ (prefixWord ++ tailWord_7411097).sum := by decide
  have hdescent : baseEnd_7411097 < baseStart_7411097 := by decide
  rcases family_descends (prefixWord ++ tailWord_7411097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7411101 : List Nat := [1, 4, 2, 1, 3, 1, 2, 3, 2, 4]
def baseStart_7411101 : Nat := 118140960795 + 7411101 * 2 ^ 59
def prefixEnd_7411101 : Nat := 4983230072969 + 3 ^ 40 * 7411101 * 2
def baseEnd_7411101 : Nat := 1268485664005571255651491

theorem tailTrace_7411101 : CollatzResearch.WordTrace tailWord_7411101 prefixEnd_7411101 1268485664005571255651491 := by
  unfold tailWord_7411101
  simp only [CollatzResearch.WordTrace]
  refine ⟨270305059923854267127169157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180203373282569511418112771 270305059923854267127169157)
  ·
    refine ⟨50682198735722675086344217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 270305059923854267127169157 50682198735722675086344217)
    ·
      refine ⟨38011649051792006314758163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50682198735722675086344217 38011649051792006314758163)
      ·
        refine ⟨57017473577688009472137245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38011649051792006314758163 57017473577688009472137245)
        ·
          refine ⟨21381552591633003552051467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57017473577688009472137245 21381552591633003552051467)
          ·
            refine ⟨32072328887449505328077201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21381552591633003552051467 32072328887449505328077201)
            ·
              refine ⟨24054246665587128996057901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32072328887449505328077201 24054246665587128996057901)
              ·
                refine ⟨9020342499595173373521713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24054246665587128996057901 9020342499595173373521713)
                ·
                  refine ⟨6765256874696380030141285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9020342499595173373521713 6765256874696380030141285)
                  ·
                    refine ⟨1268485664005571255651491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6765256874696380030141285 1268485664005571255651491)
                    ·
                      rfl

theorem cell23_7411101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 2, 3, 2, 4].length) (baseStart_7411101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7411101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7411101 prefixEnd_7411101 := by exact prefixLift 7411101
  have htrace : WordTrace (prefixWord ++ tailWord_7411101) baseStart_7411101 baseEnd_7411101 := by
    simpa [prefixWord, tailWord_7411101, baseEnd_7411101] using wordTrace_append hprefix tailTrace_7411101
  have hstable : (prefixWord ++ tailWord_7411101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7411101).length < 2 ^ (prefixWord ++ tailWord_7411101).sum := by decide
  have hdescent : baseEnd_7411101 < baseStart_7411101 := by decide
  rcases family_descends (prefixWord ++ tailWord_7411101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7411104 : List Nat := [2, 1, 1, 4, 1, 2, 4, 1, 1, 2, 4]
def baseStart_7411104 : Nat := 118140960795 + 7411104 * 2 ^ 59
def prefixEnd_7411104 : Nat := 4983230072969 + 3 ^ 40 * 7411104 * 2
def baseEnd_7411104 : Nat := 3805458532458677255216959

theorem tailTrace_7411104 : CollatzResearch.WordTrace tailWord_7411104 prefixEnd_7411104 3805458532458677255216959 := by
  unfold tailWord_7411104
  simp only [CollatzResearch.WordTrace]
  refine ⟨135152584671421699319764183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180203446228562265759685577 135152584671421699319764183)
  ·
    refine ⟨202728877007132548979646275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135152584671421699319764183 202728877007132548979646275)
    ·
      refine ⟨304093315510698823469469413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202728877007132548979646275 304093315510698823469469413)
      ·
        refine ⟨57017496658256029400525515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 304093315510698823469469413 57017496658256029400525515)
        ·
          refine ⟨85526244987384044100788273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57017496658256029400525515 85526244987384044100788273)
          ·
            refine ⟨64144683740538033075591205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85526244987384044100788273 64144683740538033075591205)
            ·
              refine ⟨12027128201350881201673351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 64144683740538033075591205 12027128201350881201673351)
              ·
                refine ⟨18040692302026321802510027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12027128201350881201673351 18040692302026321802510027)
                ·
                  refine ⟨27061038453039482703765041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18040692302026321802510027 27061038453039482703765041)
                  ·
                    refine ⟨20295778839779612027823781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27061038453039482703765041 20295778839779612027823781)
                    ·
                      refine ⟨3805458532458677255216959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20295778839779612027823781 3805458532458677255216959)
                      ·
                        rfl

theorem cell23_7411104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 4, 1, 1, 2, 4].length) (baseStart_7411104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7411104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7411104 prefixEnd_7411104 := by exact prefixLift 7411104
  have htrace : WordTrace (prefixWord ++ tailWord_7411104) baseStart_7411104 baseEnd_7411104 := by
    simpa [prefixWord, tailWord_7411104, baseEnd_7411104] using wordTrace_append hprefix tailTrace_7411104
  have hstable : (prefixWord ++ tailWord_7411104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7411104).length < 2 ^ (prefixWord ++ tailWord_7411104).sum := by decide
  have hdescent : baseEnd_7411104 < baseStart_7411104 := by decide
  rcases family_descends (prefixWord ++ tailWord_7411104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7411111 : List Nat := [1, 1, 6, 1, 1, 1, 2, 4, 1, 2, 3]
def baseStart_7411111 : Nat := 118140960795 + 7411111 * 2 ^ 59
def prefixEnd_7411111 : Nat := 4983230072969 + 3 ^ 40 * 7411111 * 2
def baseEnd_7411111 : Nat := 3805462126823258727829427

theorem tailTrace_7411111 : CollatzResearch.WordTrace tailWord_7411111 prefixEnd_7411111 3805462126823258727829427 := by
  unfold tailWord_7411111
  simp only [CollatzResearch.WordTrace]
  refine ⟨270305424653818038835033187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180203616435878692556688791 270305424653818038835033187)
  ·
    refine ⟨405458136980727058252549781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270305424653818038835033187 405458136980727058252549781)
    ·
      refine ⟨19005850170971580855588271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 405458136980727058252549781 19005850170971580855588271)
      ·
        refine ⟨28508775256457371283382407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19005850170971580855588271 28508775256457371283382407)
        ·
          refine ⟨42763162884686056925073611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28508775256457371283382407 42763162884686056925073611)
          ·
            refine ⟨64144744327029085387610417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42763162884686056925073611 64144744327029085387610417)
            ·
              refine ⟨48108558245271814040707813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64144744327029085387610417 48108558245271814040707813)
              ·
                refine ⟨9020354670988465132632715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48108558245271814040707813 9020354670988465132632715)
                ·
                  refine ⟨13530532006482697698949073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9020354670988465132632715 13530532006482697698949073)
                  ·
                    refine ⟨10147899004862023274211805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13530532006482697698949073 10147899004862023274211805)
                    ·
                      refine ⟨3805462126823258727829427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10147899004862023274211805 3805462126823258727829427)
                      ·
                        rfl

theorem cell23_7411111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 2, 4, 1, 2, 3].length) (baseStart_7411111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7411111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7411111 prefixEnd_7411111 := by exact prefixLift 7411111
  have htrace : WordTrace (prefixWord ++ tailWord_7411111) baseStart_7411111 baseEnd_7411111 := by
    simpa [prefixWord, tailWord_7411111, baseEnd_7411111] using wordTrace_append hprefix tailTrace_7411111
  have hstable : (prefixWord ++ tailWord_7411111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7411111).length < 2 ^ (prefixWord ++ tailWord_7411111).sum := by decide
  have hdescent : baseEnd_7411111 < baseStart_7411111 := by decide
  rcases family_descends (prefixWord ++ tailWord_7411111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7411112 : List Nat := [2, 1, 6, 1, 3, 1, 1, 1, 2, 3, 2]
def baseStart_7411112 : Nat := 118140960795 + 7411112 * 2 ^ 59
def prefixEnd_7411112 : Nat := 4983230072969 + 3 ^ 40 * 7411112 * 2
def baseEnd_7411112 : Nat := 3805462640303913223916923

theorem tailTrace_7411112 : CollatzResearch.WordTrace tailWord_7411112 prefixEnd_7411112 3805462640303913223916923 := by
  unfold tailWord_7411112
  simp only [CollatzResearch.WordTrace]
  refine ⟨135152730563407208002909795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180203640751209610670546393 135152730563407208002909795)
  ·
    refine ⟨202729095845110812004364693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135152730563407208002909795 202729095845110812004364693)
    ·
      refine ⟨9502926367739569312704595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 202729095845110812004364693 9502926367739569312704595)
      ·
        refine ⟨14254389551609353969056893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9502926367739569312704595 14254389551609353969056893)
        ·
          refine ⟨5345396081853507738396335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14254389551609353969056893 5345396081853507738396335)
          ·
            refine ⟨8018094122780261607594503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5345396081853507738396335 8018094122780261607594503)
            ·
              refine ⟨12027141184170392411391755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8018094122780261607594503 12027141184170392411391755)
              ·
                refine ⟨18040711776255588617087633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12027141184170392411391755 18040711776255588617087633)
                ·
                  refine ⟨13530533832191691462815725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18040711776255588617087633 13530533832191691462815725)
                  ·
                    refine ⟨5073950187071884298555897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13530533832191691462815725 5073950187071884298555897)
                    ·
                      refine ⟨3805462640303913223916923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5073950187071884298555897 3805462640303913223916923)
                      ·
                        rfl

theorem cell23_7411112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 3, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 3, 1, 1, 1, 2, 3, 2].length) (baseStart_7411112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7411112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7411112 prefixEnd_7411112 := by exact prefixLift 7411112
  have htrace : WordTrace (prefixWord ++ tailWord_7411112) baseStart_7411112 baseEnd_7411112 := by
    simpa [prefixWord, tailWord_7411112, baseEnd_7411112] using wordTrace_append hprefix tailTrace_7411112
  have hstable : (prefixWord ++ tailWord_7411112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7411112).length < 2 ^ (prefixWord ++ tailWord_7411112).sum := by decide
  have hdescent : baseEnd_7411112 < baseStart_7411112 := by decide
  rcases family_descends (prefixWord ++ tailWord_7411112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7411125 : List Nat := [1, 3, 3, 2, 2, 1, 1, 5, 1, 2, 2]
def baseStart_7411125 : Nat := 118140960795 + 7411125 * 2 ^ 59
def prefixEnd_7411125 : Nat := 4983230072969 + 3 ^ 40 * 7411125 * 2
def baseEnd_7411125 : Nat := 3805469315552421673054363

theorem tailTrace_7411125 : CollatzResearch.WordTrace tailWord_7411125 prefixEnd_7411125 3805469315552421673054363 := by
  unfold tailWord_7411125
  simp only [CollatzResearch.WordTrace]
  refine ⟨270305935275767319226042829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180203956850511546150695219 270305935275767319226042829)
  ·
    refine ⟨101364725728412744709766061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 270305935275767319226042829 101364725728412744709766061)
    ·
      refine ⟨38011772148154779266162273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 101364725728412744709766061 38011772148154779266162273)
      ·
        refine ⟨28508829111116084449621705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38011772148154779266162273 28508829111116084449621705)
        ·
          refine ⟨21381621833337063337216279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28508829111116084449621705 21381621833337063337216279)
          ·
            refine ⟨32072432750005595005824419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21381621833337063337216279 32072432750005595005824419)
            ·
              refine ⟨48108649125008392508736629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32072432750005595005824419 48108649125008392508736629)
              ·
                refine ⟨4510185855469536797694059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 48108649125008392508736629 4510185855469536797694059)
                ·
                  refine ⟨6765278783204305196541089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4510185855469536797694059 6765278783204305196541089)
                  ·
                    refine ⟨5073959087403228897405817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6765278783204305196541089 5073959087403228897405817)
                    ·
                      refine ⟨3805469315552421673054363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5073959087403228897405817 3805469315552421673054363)
                      ·
                        rfl

theorem cell23_7411125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 1, 5, 1, 2, 2].length) (baseStart_7411125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7411125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7411125 prefixEnd_7411125 := by exact prefixLift 7411125
  have htrace : WordTrace (prefixWord ++ tailWord_7411125) baseStart_7411125 baseEnd_7411125 := by
    simpa [prefixWord, tailWord_7411125, baseEnd_7411125] using wordTrace_append hprefix tailTrace_7411125
  have hstable : (prefixWord ++ tailWord_7411125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7411125).length < 2 ^ (prefixWord ++ tailWord_7411125).sum := by decide
  have hdescent : baseEnd_7411125 < baseStart_7411125 := by decide
  rcases family_descends (prefixWord ++ tailWord_7411125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7411147 : List Nat := [1, 1, 1, 1, 3, 3, 2, 1, 1, 5, 4]
def baseStart_7411147 : Nat := 118140960795 + 7411147 * 2 ^ 59
def prefixEnd_7411147 : Nat := 4983230072969 + 3 ^ 40 * 7411147 * 2
def baseEnd_7411147 : Nat := 3805480612126820586979261

theorem tailTrace_7411147 : CollatzResearch.WordTrace tailWord_7411147 prefixEnd_7411147 3805480612126820586979261 := by
  unfold tailWord_7411147
  simp only [CollatzResearch.WordTrace]
  refine ⟨270306737681687616983343695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180204491787791744655562463 270306737681687616983343695)
  ·
    refine ⟨405460106522531425475015543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270306737681687616983343695 405460106522531425475015543)
    ·
      refine ⟨608190159783797138212523315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 405460106522531425475015543 608190159783797138212523315)
      ·
        refine ⟨912285239675695707318784973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 608190159783797138212523315 912285239675695707318784973)
        ·
          refine ⟨342106964878385890244544365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 912285239675695707318784973 342106964878385890244544365)
          ·
            refine ⟨128290111829394708841704137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 342106964878385890244544365 128290111829394708841704137)
            ·
              refine ⟨96217583872046031631278103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 128290111829394708841704137 96217583872046031631278103)
              ·
                refine ⟨144326375808069047446917155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 96217583872046031631278103 144326375808069047446917155)
                ·
                  refine ⟨216489563712103571170375733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 144326375808069047446917155 216489563712103571170375733)
                  ·
                    refine ⟨20295896598009709797222725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 216489563712103571170375733 20295896598009709797222725)
                    ·
                      refine ⟨3805480612126820586979261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20295896598009709797222725 3805480612126820586979261)
                      ·
                        rfl

theorem cell23_7411147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 1, 1, 5, 4].length) (baseStart_7411147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7411147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7411147 prefixEnd_7411147 := by exact prefixLift 7411147
  have htrace : WordTrace (prefixWord ++ tailWord_7411147) baseStart_7411147 baseEnd_7411147 := by
    simpa [prefixWord, tailWord_7411147, baseEnd_7411147] using wordTrace_append hprefix tailTrace_7411147
  have hstable : (prefixWord ++ tailWord_7411147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7411147).length < 2 ^ (prefixWord ++ tailWord_7411147).sum := by decide
  have hdescent : baseEnd_7411147 < baseStart_7411147 := by decide
  rcases family_descends (prefixWord ++ tailWord_7411147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7411158 : List Nat := [5, 2, 1, 1, 1, 2, 3, 1, 1, 3, 3]
def baseStart_7411158 : Nat := 118140960795 + 7411158 * 2 ^ 59
def prefixEnd_7411158 : Nat := 4983230072969 + 3 ^ 40 * 7411158 * 2
def baseEnd_7411158 : Nat := 3805486260414020043941711

theorem tailTrace_7411158 : CollatzResearch.WordTrace tailWord_7411158 prefixEnd_7411158 3805486260414020043941711 := by
  unfold tailWord_7411158
  simp only [CollatzResearch.WordTrace]
  refine ⟨16894196180290485366374633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 180204759256431843907996085 16894196180290485366374633)
  ·
    refine ⟨12670647135217864024780975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16894196180290485366374633 12670647135217864024780975)
    ·
      refine ⟨19005970702826796037171463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12670647135217864024780975 19005970702826796037171463)
      ·
        refine ⟨28508956054240194055757195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19005970702826796037171463 28508956054240194055757195)
        ·
          refine ⟨42763434081360291083635793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28508956054240194055757195 42763434081360291083635793)
          ·
            refine ⟨32072575561020218312726845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42763434081360291083635793 32072575561020218312726845)
            ·
              refine ⟨12027215835382581867272567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32072575561020218312726845 12027215835382581867272567)
              ·
                refine ⟨18040823753073872800908851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12027215835382581867272567 18040823753073872800908851)
                ·
                  refine ⟨27061235629610809201363277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18040823753073872800908851 27061235629610809201363277)
                  ·
                    refine ⟨10147963361104053450511229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27061235629610809201363277 10147963361104053450511229)
                    ·
                      refine ⟨3805486260414020043941711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10147963361104053450511229 3805486260414020043941711)
                      ·
                        rfl

theorem cell23_7411158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 3, 1, 1, 3, 3].length) (baseStart_7411158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7411158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7411158 prefixEnd_7411158 := by exact prefixLift 7411158
  have htrace : WordTrace (prefixWord ++ tailWord_7411158) baseStart_7411158 baseEnd_7411158 := by
    simpa [prefixWord, tailWord_7411158, baseEnd_7411158] using wordTrace_append hprefix tailTrace_7411158
  have hstable : (prefixWord ++ tailWord_7411158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7411158).length < 2 ^ (prefixWord ++ tailWord_7411158).sum := by decide
  have hdescent : baseEnd_7411158 < baseStart_7411158 := by decide
  rcases family_descends (prefixWord ++ tailWord_7411158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7411184 : List Nat := [2, 1, 1, 1, 3, 5, 1, 1, 2, 1, 5]
def baseStart_7411184 : Nat := 118140960795 + 7411184 * 2 ^ 59
def prefixEnd_7411184 : Nat := 4983230072969 + 3 ^ 40 * 7411184 * 2
def baseEnd_7411184 : Nat := 3805499610911036942216591

theorem tailTrace_7411184 : CollatzResearch.WordTrace tailWord_7411184 prefixEnd_7411184 3805499610911036942216591 := by
  unfold tailWord_7411184
  simp only [CollatzResearch.WordTrace]
  refine ⟨135154043591276786151220303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180205391455035714868293737 135154043591276786151220303)
  ·
    refine ⟨202731065386915179226830455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135154043591276786151220303 202731065386915179226830455)
    ·
      refine ⟨304096598080372768840245683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202731065386915179226830455 304096598080372768840245683)
      ·
        refine ⟨456144897120559153260368525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 304096598080372768840245683 456144897120559153260368525)
        ·
          refine ⟨171054336420209682472638197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 456144897120559153260368525 171054336420209682472638197)
          ·
            refine ⟨16036344039394657731809831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 171054336420209682472638197 16036344039394657731809831)
            ·
              refine ⟨24054516059091986597714747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16036344039394657731809831 24054516059091986597714747)
              ·
                refine ⟨36081774088637979896572121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24054516059091986597714747 36081774088637979896572121)
                ·
                  refine ⟨27061330566478484922429091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36081774088637979896572121 27061330566478484922429091)
                  ·
                    refine ⟨40591995849717727383643637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27061330566478484922429091 40591995849717727383643637)
                    ·
                      refine ⟨3805499610911036942216591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40591995849717727383643637 3805499610911036942216591)
                      ·
                        rfl

theorem cell23_7411184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 1, 1, 2, 1, 5].length) (baseStart_7411184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7411184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7411184 prefixEnd_7411184 := by exact prefixLift 7411184
  have htrace : WordTrace (prefixWord ++ tailWord_7411184) baseStart_7411184 baseEnd_7411184 := by
    simpa [prefixWord, tailWord_7411184, baseEnd_7411184] using wordTrace_append hprefix tailTrace_7411184
  have hstable : (prefixWord ++ tailWord_7411184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7411184).length < 2 ^ (prefixWord ++ tailWord_7411184).sum := by decide
  have hdescent : baseEnd_7411184 < baseStart_7411184 := by decide
  rcases family_descends (prefixWord ++ tailWord_7411184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7411234 : List Nat := [3, 3, 1, 1, 1, 1, 2, 3, 1, 7]
def baseStart_7411234 : Nat := 118140960795 + 7411234 * 2 ^ 59
def prefixEnd_7411234 : Nat := 4983230072969 + 3 ^ 40 * 7411234 * 2
def baseEnd_7411234 : Nat := 1268508428314587248863787

theorem tailTrace_7411234 : CollatzResearch.WordTrace tailWord_7411234 prefixEnd_7411234 1268508428314587248863787 := by
  unfold tailWord_7411234
  simp only [CollatzResearch.WordTrace]
  refine ⟨67577477708093107710440189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 180206607221581620561173837 67577477708093107710440189)
  ·
    refine ⟨25341554140534915391415071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67577477708093107710440189 25341554140534915391415071)
    ·
      refine ⟨38012331210802373087122607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25341554140534915391415071 38012331210802373087122607)
      ·
        refine ⟨57018496816203559630683911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38012331210802373087122607 57018496816203559630683911)
        ·
          refine ⟨85527745224305339446025867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57018496816203559630683911 85527745224305339446025867)
          ·
            refine ⟨128291617836458009169038801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85527745224305339446025867 128291617836458009169038801)
            ·
              refine ⟨96218713377343506876779101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 128291617836458009169038801 96218713377343506876779101)
              ·
                refine ⟨36082017516503815078792163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 96218713377343506876779101 36082017516503815078792163)
                ·
                  refine ⟨54123026274755722618188245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36082017516503815078792163 54123026274755722618188245)
                  ·
                    refine ⟨1268508428314587248863787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 54123026274755722618188245 1268508428314587248863787)
                    ·
                      rfl

theorem cell23_7411234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 3, 1, 7].length) (baseStart_7411234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7411234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7411234 prefixEnd_7411234 := by exact prefixLift 7411234
  have htrace : WordTrace (prefixWord ++ tailWord_7411234) baseStart_7411234 baseEnd_7411234 := by
    simpa [prefixWord, tailWord_7411234, baseEnd_7411234] using wordTrace_append hprefix tailTrace_7411234
  have hstable : (prefixWord ++ tailWord_7411234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7411234).length < 2 ^ (prefixWord ++ tailWord_7411234).sum := by decide
  have hdescent : baseEnd_7411234 < baseStart_7411234 := by decide
  rcases family_descends (prefixWord ++ tailWord_7411234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7411281 : List Nat := [1, 2, 2, 1, 3, 2, 3, 2, 3, 4]
def baseStart_7411281 : Nat := 118140960795 + 7411281 * 2 ^ 59
def prefixEnd_7411281 : Nat := 4983230072969 + 3 ^ 40 * 7411281 * 2
def baseEnd_7411281 : Nat := 1268516472844841020901215

theorem tailTrace_7411281 : CollatzResearch.WordTrace tailWord_7411281 prefixEnd_7411281 1268516472844841020901215 := by
  unfold tailWord_7411281
  simp only [CollatzResearch.WordTrace]
  refine ⟨270311625063202157868721697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180207750042134771912481131 270311625063202157868721697)
  ·
    refine ⟨202733718797401618401541273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 270311625063202157868721697 202733718797401618401541273)
    ·
      refine ⟨152050289098051213801155955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 202733718797401618401541273 152050289098051213801155955)
      ·
        refine ⟨228075433647076820701733933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152050289098051213801155955 228075433647076820701733933)
        ·
          refine ⟨85528287617653807763150225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 228075433647076820701733933 85528287617653807763150225)
          ·
            refine ⟨64146215713240355822362669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85528287617653807763150225 64146215713240355822362669)
            ·
              refine ⟨24054830892465133433386001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64146215713240355822362669 24054830892465133433386001)
              ·
                refine ⟨18041123169348850075039501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24054830892465133433386001 18041123169348850075039501)
                ·
                  refine ⟨6765421188505818778139813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18041123169348850075039501 6765421188505818778139813)
                  ·
                    refine ⟨1268516472844841020901215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6765421188505818778139813 1268516472844841020901215)
                    ·
                      rfl

theorem cell23_7411281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 3, 2, 3, 4].length) (baseStart_7411281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7411281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7411281 prefixEnd_7411281 := by exact prefixLift 7411281
  have htrace : WordTrace (prefixWord ++ tailWord_7411281) baseStart_7411281 baseEnd_7411281 := by
    simpa [prefixWord, tailWord_7411281, baseEnd_7411281] using wordTrace_append hprefix tailTrace_7411281
  have hstable : (prefixWord ++ tailWord_7411281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7411281).length < 2 ^ (prefixWord ++ tailWord_7411281).sum := by decide
  have hdescent : baseEnd_7411281 < baseStart_7411281 := by decide
  rcases family_descends (prefixWord ++ tailWord_7411281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7411344 : List Nat := [2, 1, 1, 1, 1, 1, 3, 2, 2, 5, 4]
def baseStart_7411344 : Nat := 118140960795 + 7411344 * 2 ^ 59
def prefixEnd_7411344 : Nat := 4983230072969 + 3 ^ 40 * 7411344 * 2
def baseEnd_7411344 : Nat := 3805581767815756316215855

theorem tailTrace_7411344 : CollatzResearch.WordTrace tailWord_7411344 prefixEnd_7411344 3805581767815756316215855 := by
  unfold tailWord_7411344
  simp only [CollatzResearch.WordTrace]
  refine ⟨135156961430986959814132543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180209281907982613085510057 135156961430986959814132543)
  ·
    refine ⟨202735442146480439721198815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135156961430986959814132543 202735442146480439721198815)
    ·
      refine ⟨304103163219720659581798223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202735442146480439721198815 304103163219720659581798223)
      ·
        refine ⟨456154744829580989372697335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 304103163219720659581798223 456154744829580989372697335)
        ·
          refine ⟨684232117244371484059046003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 456154744829580989372697335 684232117244371484059046003)
          ·
            refine ⟨1026348175866557226088569005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 684232117244371484059046003 1026348175866557226088569005)
            ·
              refine ⟨384880565949958959783213377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1026348175866557226088569005 384880565949958959783213377)
              ·
                refine ⟨288660424462469219837410033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 384880565949958959783213377 288660424462469219837410033)
                ·
                  refine ⟨216495318346851914878057525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 288660424462469219837410033 216495318346851914878057525)
                  ·
                    refine ⟨20296436095017367019817893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 216495318346851914878057525 20296436095017367019817893)
                    ·
                      refine ⟨3805581767815756316215855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20296436095017367019817893 3805581767815756316215855)
                      ·
                        rfl

theorem cell23_7411344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 2, 2, 5, 4].length) (baseStart_7411344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7411344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7411344 prefixEnd_7411344 := by exact prefixLift 7411344
  have htrace : WordTrace (prefixWord ++ tailWord_7411344) baseStart_7411344 baseEnd_7411344 := by
    simpa [prefixWord, tailWord_7411344, baseEnd_7411344] using wordTrace_append hprefix tailTrace_7411344
  have hstable : (prefixWord ++ tailWord_7411344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7411344).length < 2 ^ (prefixWord ++ tailWord_7411344).sum := by decide
  have hdescent : baseEnd_7411344 < baseStart_7411344 := by decide
  rcases family_descends (prefixWord ++ tailWord_7411344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7411391 : List Nat := [1, 1, 2, 2, 2, 3, 2, 3, 1, 2, 4]
def baseStart_7411391 : Nat := 118140960795 + 7411391 * 2 ^ 59
def prefixEnd_7411391 : Nat := 4983230072969 + 3 ^ 40 * 7411391 * 2
def baseEnd_7411391 : Nat := 3805605901406517632328139

theorem tailTrace_7411391 : CollatzResearch.WordTrace tailWord_7411391 prefixEnd_7411391 3805605901406517632328139 := by
  unfold tailWord_7411391
  simp only [CollatzResearch.WordTrace]
  refine ⟨270315637092803646655226027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180210424728535764436817351 270315637092803646655226027)
  ·
    refine ⟨405473455639205469982839041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270315637092803646655226027 405473455639205469982839041)
    ·
      refine ⟨304105091729404102487129281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 405473455639205469982839041 304105091729404102487129281)
      ·
        refine ⟨228078818797053076865346961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 304105091729404102487129281 228078818797053076865346961)
        ·
          refine ⟨171059114097789807649010221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 228078818797053076865346961 171059114097789807649010221)
          ·
            refine ⟨64147167786671177868378833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 171059114097789807649010221 64147167786671177868378833)
            ·
              refine ⟨48110375840003383401284125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64147167786671177868378833 48110375840003383401284125)
              ·
                refine ⟨18041390940001268775481547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48110375840003383401284125 18041390940001268775481547)
                ·
                  refine ⟨27062086410001903163222321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18041390940001268775481547 27062086410001903163222321)
                  ·
                    refine ⟨20296564807501427372416741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27062086410001903163222321 20296564807501427372416741)
                    ·
                      refine ⟨3805605901406517632328139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20296564807501427372416741 3805605901406517632328139)
                      ·
                        rfl

theorem cell23_7411391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 2, 3, 1, 2, 4].length) (baseStart_7411391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7411391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7411391 prefixEnd_7411391 := by exact prefixLift 7411391
  have htrace : WordTrace (prefixWord ++ tailWord_7411391) baseStart_7411391 baseEnd_7411391 := by
    simpa [prefixWord, tailWord_7411391, baseEnd_7411391] using wordTrace_append hprefix tailTrace_7411391
  have hstable : (prefixWord ++ tailWord_7411391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7411391).length < 2 ^ (prefixWord ++ tailWord_7411391).sum := by decide
  have hdescent : baseEnd_7411391 < baseStart_7411391 := by decide
  rcases family_descends (prefixWord ++ tailWord_7411391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7411405 : List Nat := [1, 6, 2, 1, 1, 2, 1, 2, 1, 6]
def baseStart_7411405 : Nat := 118140960795 + 7411405 * 2 ^ 59
def prefixEnd_7411405 : Nat := 4983230072969 + 3 ^ 40 * 7411405 * 2
def baseEnd_7411405 : Nat := 1268537696711893525851025

theorem tailTrace_7411405 : CollatzResearch.WordTrace tailWord_7411405 prefixEnd_7411405 1268537696711893525851025 := by
  unfold tailWord_7411405
  simp only [CollatzResearch.WordTrace]
  refine ⟨270316147714752927046235669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180210765143168618030823779 270316147714752927046235669)
  ·
    refine ⟨12671069424129043455292297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 270316147714752927046235669 12671069424129043455292297)
    ·
      refine ⟨9503302068096782591469223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12671069424129043455292297 9503302068096782591469223)
      ·
        refine ⟨14254953102145173887203835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9503302068096782591469223 14254953102145173887203835)
        ·
          refine ⟨21382429653217760830805753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14254953102145173887203835 21382429653217760830805753)
          ·
            refine ⟨16036822239913320623104315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21382429653217760830805753 16036822239913320623104315)
            ·
              refine ⟨24055233359869980934656473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16036822239913320623104315 24055233359869980934656473)
              ·
                refine ⟨18041425019902485700992355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24055233359869980934656473 18041425019902485700992355)
                ·
                  refine ⟨27062137529853728551488533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18041425019902485700992355 27062137529853728551488533)
                  ·
                    refine ⟨1268537696711893525851025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27062137529853728551488533 1268537696711893525851025)
                    ·
                      rfl

theorem cell23_7411405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 1, 2, 1, 6].length) (baseStart_7411405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7411405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7411405 prefixEnd_7411405 := by exact prefixLift 7411405
  have htrace : WordTrace (prefixWord ++ tailWord_7411405) baseStart_7411405 baseEnd_7411405 := by
    simpa [prefixWord, tailWord_7411405, baseEnd_7411405] using wordTrace_append hprefix tailTrace_7411405
  have hstable : (prefixWord ++ tailWord_7411405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7411405).length < 2 ^ (prefixWord ++ tailWord_7411405).sum := by decide
  have hdescent : baseEnd_7411405 < baseStart_7411405 := by decide
  rcases family_descends (prefixWord ++ tailWord_7411405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7411412 : List Nat := [2, 4, 1, 3, 1, 2, 3, 1, 1, 1, 4]
def baseStart_7411412 : Nat := 118140960795 + 7411412 * 2 ^ 59
def prefixEnd_7411412 : Nat := 4983230072969 + 3 ^ 40 * 7411412 * 2
def baseEnd_7411412 : Nat := 3805616684500262050165543

theorem tailTrace_7411412 : CollatzResearch.WordTrace tailWord_7411412 prefixEnd_7411412 3805616684500262050165543 := by
  unfold tailWord_7411412
  simp only [CollatzResearch.WordTrace]
  refine ⟨135158201512863783620870245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180210935350485044827826993 135158201512863783620870245)
  ·
    refine ⟨25342162783661959428913171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 135158201512863783620870245 25342162783661959428913171)
    ·
      refine ⟨38013244175492939143369757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25342162783661959428913171 38013244175492939143369757)
      ·
        refine ⟨14254966565809852178763659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38013244175492939143369757 14254966565809852178763659)
        ·
          refine ⟨21382449848714778268145489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14254966565809852178763659 21382449848714778268145489)
          ·
            refine ⟨16036837386536083701109117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21382449848714778268145489 16036837386536083701109117)
            ·
              refine ⟨6013814019951031387915919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16036837386536083701109117 6013814019951031387915919)
              ·
                refine ⟨9020721029926547081873879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6013814019951031387915919 9020721029926547081873879)
                ·
                  refine ⟨13531081544889820622810819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9020721029926547081873879 13531081544889820622810819)
                  ·
                    refine ⟨20296622317334730934216229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13531081544889820622810819 20296622317334730934216229)
                    ·
                      refine ⟨3805616684500262050165543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20296622317334730934216229 3805616684500262050165543)
                      ·
                        rfl

theorem cell23_7411412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 3, 1, 1, 1, 4].length) (baseStart_7411412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7411412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7411412 prefixEnd_7411412 := by exact prefixLift 7411412
  have htrace : WordTrace (prefixWord ++ tailWord_7411412) baseStart_7411412 baseEnd_7411412 := by
    simpa [prefixWord, tailWord_7411412, baseEnd_7411412] using wordTrace_append hprefix tailTrace_7411412
  have hstable : (prefixWord ++ tailWord_7411412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7411412).length < 2 ^ (prefixWord ++ tailWord_7411412).sum := by decide
  have hdescent : baseEnd_7411412 < baseStart_7411412 := by decide
  rcases family_descends (prefixWord ++ tailWord_7411412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7411415 : List Nat := [1, 1, 3, 2, 1, 3, 5, 1, 1, 2, 3]
def baseStart_7411415 : Nat := 118140960795 + 7411415 * 2 ^ 59
def prefixEnd_7411415 : Nat := 4983230072969 + 3 ^ 40 * 7411415 * 2
def baseEnd_7411415 : Nat := 3805618224942225538428029

theorem tailTrace_7411415 : CollatzResearch.WordTrace tailWord_7411415 prefixEnd_7411415 3805618224942225538428029 := by
  unfold tailWord_7411415
  simp only [CollatzResearch.WordTrace]
  refine ⟨270316512444716698754099699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180211008296477799169399799 270316512444716698754099699)
  ·
    refine ⟨405474768667075048131149549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270316512444716698754099699 405474768667075048131149549)
    ·
      refine ⟨152053038250153143049181081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 405474768667075048131149549 152053038250153143049181081)
      ·
        refine ⟨114039778687614857286885811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 152053038250153143049181081 114039778687614857286885811)
        ·
          refine ⟨171059668031422285930328717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114039778687614857286885811 171059668031422285930328717)
          ·
            refine ⟨64147375511783357223873269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 171059668031422285930328717 64147375511783357223873269)
            ·
              refine ⟨6013816454229689739738119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 64147375511783357223873269 6013816454229689739738119)
              ·
                refine ⟨9020724681344534609607179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6013816454229689739738119 9020724681344534609607179)
                ·
                  refine ⟨13531087022016801914410769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9020724681344534609607179 13531087022016801914410769)
                  ·
                    refine ⟨10148315266512601435808077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13531087022016801914410769 10148315266512601435808077)
                    ·
                      refine ⟨3805618224942225538428029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10148315266512601435808077 3805618224942225538428029)
                      ·
                        rfl

theorem cell23_7411415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 5, 1, 1, 2, 3].length) (baseStart_7411415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7411415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7411415 prefixEnd_7411415 := by exact prefixLift 7411415
  have htrace : WordTrace (prefixWord ++ tailWord_7411415) baseStart_7411415 baseEnd_7411415 := by
    simpa [prefixWord, tailWord_7411415, baseEnd_7411415] using wordTrace_append hprefix tailTrace_7411415
  have hstable : (prefixWord ++ tailWord_7411415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7411415).length < 2 ^ (prefixWord ++ tailWord_7411415).sum := by decide
  have hdescent : baseEnd_7411415 < baseStart_7411415 := by decide
  rcases family_descends (prefixWord ++ tailWord_7411415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7411458 : List Nat := [3, 4, 1, 1, 1, 1, 2, 1, 2, 2, 5]
def baseStart_7411458 : Nat := 118140960795 + 7411458 * 2 ^ 59
def prefixEnd_7411458 : Nat := 4983230072969 + 3 ^ 40 * 7411458 * 2
def baseEnd_7411458 : Nat := 3805640304610368870190331

theorem tailTrace_7411458 : CollatzResearch.WordTrace tailWord_7411458 prefixEnd_7411458 3805640304610368870190331 := by
  unfold tailWord_7411458
  simp only [CollatzResearch.WordTrace]
  refine ⟨67579520195890229274478757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 180212053855707278065276685 67579520195890229274478757)
  ·
    refine ⟨12671160036729417988964767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 67579520195890229274478757 12671160036729417988964767)
    ·
      refine ⟨19006740055094126983447151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12671160036729417988964767 19006740055094126983447151)
      ·
        refine ⟨28510110082641190475170727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19006740055094126983447151 28510110082641190475170727)
        ·
          refine ⟨42765165123961785712756091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28510110082641190475170727 42765165123961785712756091)
          ·
            refine ⟨64147747685942678569134137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42765165123961785712756091 64147747685942678569134137)
            ·
              refine ⟨48110810764457008926850603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64147747685942678569134137 48110810764457008926850603)
              ·
                refine ⟨72166216146685513390275905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48110810764457008926850603 72166216146685513390275905)
                ·
                  refine ⟨54124662110014135042706929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 72166216146685513390275905 54124662110014135042706929)
                  ·
                    refine ⟨40593496582510601282030197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 54124662110014135042706929 40593496582510601282030197)
                    ·
                      refine ⟨3805640304610368870190331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40593496582510601282030197 3805640304610368870190331)
                      ·
                        rfl

theorem cell23_7411458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 2, 1, 2, 2, 5].length) (baseStart_7411458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7411458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7411458 prefixEnd_7411458 := by exact prefixLift 7411458
  have htrace : WordTrace (prefixWord ++ tailWord_7411458) baseStart_7411458 baseEnd_7411458 := by
    simpa [prefixWord, tailWord_7411458, baseEnd_7411458] using wordTrace_append hprefix tailTrace_7411458
  have hstable : (prefixWord ++ tailWord_7411458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7411458).length < 2 ^ (prefixWord ++ tailWord_7411458).sum := by decide
  have hdescent : baseEnd_7411458 < baseStart_7411458 := by decide
  rcases family_descends (prefixWord ++ tailWord_7411458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7411471 : List Nat := [1, 1, 2, 1, 1, 1, 4, 2, 1, 6, 3]
def baseStart_7411471 : Nat := 118140960795 + 7411471 * 2 ^ 59
def prefixEnd_7411471 : Nat := 4983230072969 + 3 ^ 40 * 7411471 * 2
def baseEnd_7411471 : Nat := 3805646979858877319327771

theorem tailTrace_7411471 : CollatzResearch.WordTrace tailWord_7411471 prefixEnd_7411471 3805646979858877319327771 := by
  unfold tailWord_7411471
  simp only [CollatzResearch.WordTrace]
  refine ⟨270318554932513820318138267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180212369955009213545425511 270318554932513820318138267)
  ·
    refine ⟨405477832398770730477207401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270318554932513820318138267 405477832398770730477207401)
    ·
      refine ⟨304108374299078047857905551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 405477832398770730477207401 304108374299078047857905551)
      ·
        refine ⟨456162561448617071786858327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 304108374299078047857905551 456162561448617071786858327)
        ·
          refine ⟨684243842172925607680287491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 456162561448617071786858327 684243842172925607680287491)
          ·
            refine ⟨1026365763259388411520431237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 684243842172925607680287491 1026365763259388411520431237)
            ·
              refine ⟨192443580611135327160080857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1026365763259388411520431237 192443580611135327160080857)
              ·
                refine ⟨144332685458351495370060643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 192443580611135327160080857 144332685458351495370060643)
                ·
                  refine ⟨216499028187527243055090965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 144332685458351495370060643 216499028187527243055090965)
                  ·
                    refine ⟨10148391946290339518207389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 216499028187527243055090965 10148391946290339518207389)
                    ·
                      refine ⟨3805646979858877319327771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10148391946290339518207389 3805646979858877319327771)
                      ·
                        rfl

theorem cell23_7411471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 2, 1, 6, 3].length) (baseStart_7411471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7411471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7411471 prefixEnd_7411471 := by exact prefixLift 7411471
  have htrace : WordTrace (prefixWord ++ tailWord_7411471) baseStart_7411471 baseEnd_7411471 := by
    simpa [prefixWord, tailWord_7411471, baseEnd_7411471] using wordTrace_append hprefix tailTrace_7411471
  have hstable : (prefixWord ++ tailWord_7411471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7411471).length < 2 ^ (prefixWord ++ tailWord_7411471).sum := by decide
  have hdescent : baseEnd_7411471 < baseStart_7411471 := by decide
  rcases family_descends (prefixWord ++ tailWord_7411471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7411491 : List Nat := [1, 1, 1, 4, 2, 1, 3, 3, 7]
def baseStart_7411491 : Nat := 118140960795 + 7411491 * 2 ^ 59
def prefixEnd_7411491 : Nat := 4983230072969 + 3 ^ 40 * 7411491 * 2
def baseEnd_7411491 : Nat := 422850805496885249008631

theorem tailTrace_7411491 : CollatzResearch.WordTrace tailWord_7411491 prefixEnd_7411491 422850805496885249008631 := by
  unfold tailWord_7411491
  simp only [CollatzResearch.WordTrace]
  refine ⟨270319284392441363733866327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180212856261627575822577551 270319284392441363733866327)
  ·
    refine ⟨405478926588662045600799491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270319284392441363733866327 405478926588662045600799491)
    ·
      refine ⟨608218389882993068401199237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 405478926588662045600799491 608218389882993068401199237)
      ·
        refine ⟨114040948103061200325224857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 608218389882993068401199237 114040948103061200325224857)
        ·
          refine ⟨85530711077295900243918643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114040948103061200325224857 85530711077295900243918643)
          ·
            refine ⟨128296066615943850365877965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85530711077295900243918643 128296066615943850365877965)
            ·
              refine ⟨48111024980978943887204237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 128296066615943850365877965 48111024980978943887204237)
              ·
                refine ⟨18041634367867103957701589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48111024980978943887204237 18041634367867103957701589)
                ·
                  refine ⟨422850805496885249008631, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18041634367867103957701589 422850805496885249008631)
                  ·
                    rfl

theorem cell23_7411491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 3, 3, 7].length) (baseStart_7411491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7411491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7411491 prefixEnd_7411491 := by exact prefixLift 7411491
  have htrace : WordTrace (prefixWord ++ tailWord_7411491) baseStart_7411491 baseEnd_7411491 := by
    simpa [prefixWord, tailWord_7411491, baseEnd_7411491] using wordTrace_append hprefix tailTrace_7411491
  have hstable : (prefixWord ++ tailWord_7411491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7411491).length < 2 ^ (prefixWord ++ tailWord_7411491).sum := by decide
  have hdescent : baseEnd_7411491 < baseStart_7411491 := by decide
  rcases family_descends (prefixWord ++ tailWord_7411491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7411538 : List Nat := [3, 2, 2, 1, 1, 3, 1, 1, 4, 5]
def baseStart_7411538 : Nat := 118140960795 + 7411538 * 2 ^ 59
def prefixEnd_7411538 : Nat := 4983230072969 + 3 ^ 40 * 7411538 * 2
def baseEnd_7411538 : Nat := 1268560461020909519063321

theorem tailTrace_7411538 : CollatzResearch.WordTrace tailWord_7411538 prefixEnd_7411538 1268560461020909519063321 := by
  unfold tailWord_7411538
  simp only [CollatzResearch.WordTrace]
  refine ⟨67580249655817772690206817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 180213999082180727173884845 67580249655817772690206817)
  ·
    refine ⟨50685187241863329517655113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67580249655817772690206817 50685187241863329517655113)
    ·
      refine ⟨38013890431397497138241335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50685187241863329517655113 38013890431397497138241335)
      ·
        refine ⟨57020835647096245707362003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38013890431397497138241335 57020835647096245707362003)
        ·
          refine ⟨85531253470644368561043005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57020835647096245707362003 85531253470644368561043005)
          ·
            refine ⟨32074220051491638210391127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 85531253470644368561043005 32074220051491638210391127)
            ·
              refine ⟨48111330077237457315586691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32074220051491638210391127 48111330077237457315586691)
              ·
                refine ⟨72166995115856185973380037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48111330077237457315586691 72166995115856185973380037)
                ·
                  refine ⟨13531311584223034870008757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 72166995115856185973380037 13531311584223034870008757)
                  ·
                    refine ⟨1268560461020909519063321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13531311584223034870008757 1268560461020909519063321)
                    ·
                      rfl

theorem cell23_7411538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 1, 1, 4, 5].length) (baseStart_7411538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7411538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7411538 prefixEnd_7411538 := by exact prefixLift 7411538
  have htrace : WordTrace (prefixWord ++ tailWord_7411538) baseStart_7411538 baseEnd_7411538 := by
    simpa [prefixWord, tailWord_7411538, baseEnd_7411538] using wordTrace_append hprefix tailTrace_7411538
  have hstable : (prefixWord ++ tailWord_7411538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7411538).length < 2 ^ (prefixWord ++ tailWord_7411538).sum := by decide
  have hdescent : baseEnd_7411538 < baseStart_7411538 := by decide
  rcases family_descends (prefixWord ++ tailWord_7411538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7411561 : List Nat := [1, 2, 1, 1, 1, 3, 1, 2, 1, 5, 5]
def baseStart_7411561 : Nat := 118140960795 + 7411561 * 2 ^ 59
def prefixEnd_7411561 : Nat := 4983230072969 + 3 ^ 40 * 7411561 * 2
def baseEnd_7411561 : Nat := 3805693193117781967202357

theorem tailTrace_7411561 : CollatzResearch.WordTrace tailWord_7411561 prefixEnd_7411561 3805693193117781967202357 := by
  unfold tailWord_7411561
  simp only [CollatzResearch.WordTrace]
  refine ⟨270321837502187765688914537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180214558334791843792609691 270321837502187765688914537)
  ·
    refine ⟨202741378126640824266685903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 270321837502187765688914537 202741378126640824266685903)
    ·
      refine ⟨304112067189961236400028855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202741378126640824266685903 304112067189961236400028855)
      ·
        refine ⟨456168100784941854600043283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 304112067189961236400028855 456168100784941854600043283)
        ·
          refine ⟨684252151177412781900064925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 456168100784941854600043283 684252151177412781900064925)
          ·
            refine ⟨256594556691529793212524347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 684252151177412781900064925 256594556691529793212524347)
            ·
              refine ⟨384891835037294689818786521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 256594556691529793212524347 384891835037294689818786521)
              ·
                refine ⟨288668876277971017364089891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 384891835037294689818786521 288668876277971017364089891)
                ·
                  refine ⟨433003314416956526046134837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 288668876277971017364089891 433003314416956526046134837)
                  ·
                    refine ⟨40594060726589674316825141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 433003314416956526046134837 40594060726589674316825141)
                    ·
                      refine ⟨3805693193117781967202357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40594060726589674316825141 3805693193117781967202357)
                      ·
                        rfl

theorem cell23_7411561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 2, 1, 5, 5].length) (baseStart_7411561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7411561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7411561 prefixEnd_7411561 := by exact prefixLift 7411561
  have htrace : WordTrace (prefixWord ++ tailWord_7411561) baseStart_7411561 baseEnd_7411561 := by
    simpa [prefixWord, tailWord_7411561, baseEnd_7411561] using wordTrace_append hprefix tailTrace_7411561
  have hstable : (prefixWord ++ tailWord_7411561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7411561).length < 2 ^ (prefixWord ++ tailWord_7411561).sum := by decide
  have hdescent : baseEnd_7411561 < baseStart_7411561 := by decide
  rcases family_descends (prefixWord ++ tailWord_7411561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7411568 : List Nat := [2, 1, 1, 1, 4, 1, 1, 3, 5, 4]
def baseStart_7411568 : Nat := 118140960795 + 7411568 * 2 ^ 59
def prefixEnd_7411568 : Nat := 4983230072969 + 3 ^ 40 * 7411568 * 2
def baseEnd_7411568 : Nat := 1268565595827454479938275

theorem tailTrace_7411568 : CollatzResearch.WordTrace tailWord_7411568 prefixEnd_7411568 1268565595827454479938275 := by
  unfold tailWord_7411568
  simp only [CollatzResearch.WordTrace]
  refine ⟨135161046406581202942209679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180214728542108270589612905 135161046406581202942209679)
  ·
    refine ⟨202741569609871804413314519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135161046406581202942209679 202741569609871804413314519)
    ·
      refine ⟨304112354414807706619971779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202741569609871804413314519 304112354414807706619971779)
      ·
        refine ⟨456168531622211559929957669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 304112354414807706619971779 456168531622211559929957669)
        ·
          refine ⟨85531599679164667486867063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 456168531622211559929957669 85531599679164667486867063)
          ·
            refine ⟨128297399518747001230300595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85531599679164667486867063 128297399518747001230300595)
            ·
              refine ⟨192446099278120501845450893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 128297399518747001230300595 192446099278120501845450893)
              ·
                refine ⟨72167287229295188192044085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 192446099278120501845450893 72167287229295188192044085)
                ·
                  refine ⟨6765683177746423893004133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 72167287229295188192044085 6765683177746423893004133)
                  ·
                    refine ⟨1268565595827454479938275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6765683177746423893004133 1268565595827454479938275)
                    ·
                      rfl

theorem cell23_7411568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 3, 5, 4].length) (baseStart_7411568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7411568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7411568 prefixEnd_7411568 := by exact prefixLift 7411568
  have htrace : WordTrace (prefixWord ++ tailWord_7411568) baseStart_7411568 baseEnd_7411568 := by
    simpa [prefixWord, tailWord_7411568, baseEnd_7411568] using wordTrace_append hprefix tailTrace_7411568
  have hstable : (prefixWord ++ tailWord_7411568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7411568).length < 2 ^ (prefixWord ++ tailWord_7411568).sum := by decide
  have hdescent : baseEnd_7411568 < baseStart_7411568 := by decide
  rcases family_descends (prefixWord ++ tailWord_7411568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7411571 : List Nat := [1, 1, 1, 2, 2, 1, 3, 2, 1, 3, 6]
def baseStart_7411571 : Nat := 118140960795 + 7411571 * 2 ^ 59
def prefixEnd_7411571 : Nat := 4983230072969 + 3 ^ 40 * 7411571 * 2
def baseEnd_7411571 : Nat := 3805698327924326928077311

theorem tailTrace_7411571 : CollatzResearch.WordTrace tailWord_7411571 prefixEnd_7411571 3805698327924326928077311 := by
  unfold tailWord_7411571
  simp only [CollatzResearch.WordTrace]
  refine ⟨270322202232151537396778567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180214801488101024931185711 270322202232151537396778567)
  ·
    refine ⟨405483303348227306095167851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270322202232151537396778567 405483303348227306095167851)
    ·
      refine ⟨608224955022340959142751777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 405483303348227306095167851 608224955022340959142751777)
      ·
        refine ⟨456168716266755719357063833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 608224955022340959142751777 456168716266755719357063833)
        ·
          refine ⟨342126537200066789517797875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 456168716266755719357063833 342126537200066789517797875)
          ·
            refine ⟨513189805800100184276696813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 342126537200066789517797875 513189805800100184276696813)
            ·
              refine ⟨192446177175037569103761305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 513189805800100184276696813 192446177175037569103761305)
              ·
                refine ⟨144334632881278176827820979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 192446177175037569103761305 144334632881278176827820979)
                ·
                  refine ⟨216501949321917265241731469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 144334632881278176827820979 216501949321917265241731469)
                  ·
                    refine ⟨81188230995718974465649301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 216501949321917265241731469 81188230995718974465649301)
                    ·
                      refine ⟨3805698327924326928077311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 81188230995718974465649301 3805698327924326928077311)
                      ·
                        rfl

theorem cell23_7411571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 2, 1, 3, 6].length) (baseStart_7411571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7411571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7411571 prefixEnd_7411571 := by exact prefixLift 7411571
  have htrace : WordTrace (prefixWord ++ tailWord_7411571) baseStart_7411571 baseEnd_7411571 := by
    simpa [prefixWord, tailWord_7411571, baseEnd_7411571] using wordTrace_append hprefix tailTrace_7411571
  have hstable : (prefixWord ++ tailWord_7411571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7411571).length < 2 ^ (prefixWord ++ tailWord_7411571).sum := by decide
  have hdescent : baseEnd_7411571 < baseStart_7411571 := by decide
  rcases family_descends (prefixWord ++ tailWord_7411571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7411578 : List Nat := [3, 1, 1, 1, 1, 1, 4, 3, 1, 4, 3]
def baseStart_7411578 : Nat := 118140960795 + 7411578 * 2 ^ 59
def prefixEnd_7411578 : Nat := 4983230072969 + 3 ^ 40 * 7411578 * 2
def baseEnd_7411578 : Nat := 3805701922288908400689779

theorem tailTrace_7411578 : CollatzResearch.WordTrace tailWord_7411578 prefixEnd_7411578 3805701922288908400689779 := by
  unfold tailWord_7411578
  simp only [CollatzResearch.WordTrace]
  refine ⟨67580614385781544398070847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 180214971695417451728188925 67580614385781544398070847)
  ·
    refine ⟨101370921578672316597106271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67580614385781544398070847 101370921578672316597106271)
    ·
      refine ⟨152056382368008474895659407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101370921578672316597106271 152056382368008474895659407)
      ·
        refine ⟨228084573552012712343489111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152056382368008474895659407 228084573552012712343489111)
        ·
          refine ⟨342126860328019068515233667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 228084573552012712343489111 342126860328019068515233667)
          ·
            refine ⟨513190290492028602772850501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 342126860328019068515233667 513190290492028602772850501)
            ·
              refine ⟨96223179467255363019909469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 513190290492028602772850501 96223179467255363019909469)
              ·
                refine ⟨36083692300220761132466051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 96223179467255363019909469 36083692300220761132466051)
                ·
                  refine ⟨54125538450331141698699077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36083692300220761132466051 54125538450331141698699077)
                  ·
                    refine ⟨10148538459437089068506077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 54125538450331141698699077 10148538459437089068506077)
                    ·
                      refine ⟨3805701922288908400689779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10148538459437089068506077 3805701922288908400689779)
                      ·
                        rfl

theorem cell23_7411578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 3, 1, 4, 3].length) (baseStart_7411578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7411578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7411578 prefixEnd_7411578 := by exact prefixLift 7411578
  have htrace : WordTrace (prefixWord ++ tailWord_7411578) baseStart_7411578 baseEnd_7411578 := by
    simpa [prefixWord, tailWord_7411578, baseEnd_7411578] using wordTrace_append hprefix tailTrace_7411578
  have hstable : (prefixWord ++ tailWord_7411578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7411578).length < 2 ^ (prefixWord ++ tailWord_7411578).sum := by decide
  have hdescent : baseEnd_7411578 < baseStart_7411578 := by decide
  rcases family_descends (prefixWord ++ tailWord_7411578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7411635 : List Nat := [1, 1, 1, 2, 3, 1, 5, 1, 1, 5, 2]
def baseStart_7411635 : Nat := 118140960795 + 7411635 * 2 ^ 59
def prefixEnd_7411635 : Nat := 4983230072969 + 3 ^ 40 * 7411635 * 2
def baseEnd_7411635 : Nat := 3805731190686214677677017

theorem tailTrace_7411635 : CollatzResearch.WordTrace tailWord_7411635 prefixEnd_7411635 3805731190686214677677017 := by
  unfold tailWord_7411635
  simp only [CollatzResearch.WordTrace]
  refine ⟨270324536503919676327108359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180216357669279784218072239 270324536503919676327108359)
  ·
    refine ⟨405486804755879514490662539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270324536503919676327108359 405486804755879514490662539)
    ·
      refine ⟨608230207133819271735993809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 405486804755879514490662539 608230207133819271735993809)
      ·
        refine ⟨456172655350364453801995357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 608230207133819271735993809 456172655350364453801995357)
        ·
          refine ⟨171064745756386670175748259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 456172655350364453801995357 171064745756386670175748259)
          ·
            refine ⟨256597118634580005263622389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 171064745756386670175748259 256597118634580005263622389)
            ·
              refine ⟨24055979871991875493464599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 256597118634580005263622389 24055979871991875493464599)
              ·
                refine ⟨36083969807987813240196899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24055979871991875493464599 36083969807987813240196899)
                ·
                  refine ⟨54125954711981719860295349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36083969807987813240196899 54125954711981719860295349)
                  ·
                    refine ⟨5074308254248286236902689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 54125954711981719860295349 5074308254248286236902689)
                    ·
                      refine ⟨3805731190686214677677017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5074308254248286236902689 3805731190686214677677017)
                      ·
                        rfl

theorem cell23_7411635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 5, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 5, 1, 1, 5, 2].length) (baseStart_7411635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7411635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7411635 prefixEnd_7411635 := by exact prefixLift 7411635
  have htrace : WordTrace (prefixWord ++ tailWord_7411635) baseStart_7411635 baseEnd_7411635 := by
    simpa [prefixWord, tailWord_7411635, baseEnd_7411635] using wordTrace_append hprefix tailTrace_7411635
  have hstable : (prefixWord ++ tailWord_7411635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7411635).length < 2 ^ (prefixWord ++ tailWord_7411635).sum := by decide
  have hdescent : baseEnd_7411635 < baseStart_7411635 := by decide
  rcases family_descends (prefixWord ++ tailWord_7411635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7411658 : List Nat := [3, 1, 2, 1, 2, 1, 2, 2, 3, 6]
def baseStart_7411658 : Nat := 118140960795 + 7411658 * 2 ^ 59
def prefixEnd_7411658 : Nat := 4983230072969 + 3 ^ 40 * 7411658 * 2
def baseEnd_7411658 : Nat := 1268581000247089362563137

theorem tailTrace_7411658 : CollatzResearch.WordTrace tailWord_7411658 prefixEnd_7411658 1268581000247089362563137 := by
  unfold tailWord_7411658
  simp only [CollatzResearch.WordTrace]
  refine ⟨67581343845709087813798907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 180216916921890900836797085 67581343845709087813798907)
  ·
    refine ⟨101372015768563631720698361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67581343845709087813798907 101372015768563631720698361)
    ·
      refine ⟨76029011826422723790523771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101372015768563631720698361 76029011826422723790523771)
      ·
        refine ⟨114043517739634085685785657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76029011826422723790523771 114043517739634085685785657)
        ·
          refine ⟨85532638304725564264339243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114043517739634085685785657 85532638304725564264339243)
          ·
            refine ⟨128298957457088346396508865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85532638304725564264339243 128298957457088346396508865)
            ·
              refine ⟨96224218092816259797381649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 128298957457088346396508865 96224218092816259797381649)
              ·
                refine ⟨72168163569612194848036237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 96224218092816259797381649 72168163569612194848036237)
                ·
                  refine ⟨27063061338604573068013589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 72168163569612194848036237 27063061338604573068013589)
                  ·
                    refine ⟨1268581000247089362563137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27063061338604573068013589 1268581000247089362563137)
                    ·
                      rfl

theorem cell23_7411658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 2, 3, 6].length) (baseStart_7411658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7411658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7411658 prefixEnd_7411658 := by exact prefixLift 7411658
  have htrace : WordTrace (prefixWord ++ tailWord_7411658) baseStart_7411658 baseEnd_7411658 := by
    simpa [prefixWord, tailWord_7411658, baseEnd_7411658] using wordTrace_append hprefix tailTrace_7411658
  have hstable : (prefixWord ++ tailWord_7411658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7411658).length < 2 ^ (prefixWord ++ tailWord_7411658).sum := by decide
  have hdescent : baseEnd_7411658 < baseStart_7411658 := by decide
  rcases family_descends (prefixWord ++ tailWord_7411658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7411728 : List Nat := [2, 1, 1, 1, 1, 1, 1, 4, 4, 2, 5]
def baseStart_7411728 : Nat := 118140960795 + 7411728 * 2 ^ 59
def prefixEnd_7411728 : Nat := 4983230072969 + 3 ^ 40 * 7411728 * 2
def baseEnd_7411728 : Nat := 3805778944387082813814089

theorem tailTrace_7411728 : CollatzResearch.WordTrace tailWord_7411728 prefixEnd_7411728 3805778944387082813814089 := by
  unfold tailWord_7411728
  simp only [CollatzResearch.WordTrace]
  refine ⟨135163964246291376605121919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180218618995055168806829225 135163964246291376605121919)
  ·
    refine ⟨202745946369437064907682879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135163964246291376605121919 202745946369437064907682879)
    ·
      refine ⟨304118919554155597361524319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202745946369437064907682879 304118919554155597361524319)
      ·
        refine ⟨456178379331233396042286479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 304118919554155597361524319 456178379331233396042286479)
        ·
          refine ⟨684267568996850094063429719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 456178379331233396042286479 684267568996850094063429719)
          ·
            refine ⟨1026401353495275141095144579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 684267568996850094063429719 1026401353495275141095144579)
            ·
              refine ⟨1539602030242912711642716869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1026401353495275141095144579 1539602030242912711642716869)
              ·
                refine ⟨288675380670546133433009413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1539602030242912711642716869 288675380670546133433009413)
                ·
                  refine ⟨54126633875727400018689265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 288675380670546133433009413 54126633875727400018689265)
                  ·
                    refine ⟨40594975406795550014016949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 54126633875727400018689265 40594975406795550014016949)
                    ·
                      refine ⟨3805778944387082813814089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40594975406795550014016949 3805778944387082813814089)
                      ·
                        rfl

theorem cell23_7411728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 4, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 4, 4, 2, 5].length) (baseStart_7411728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7411728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7411728 prefixEnd_7411728 := by exact prefixLift 7411728
  have htrace : WordTrace (prefixWord ++ tailWord_7411728) baseStart_7411728 baseEnd_7411728 := by
    simpa [prefixWord, tailWord_7411728, baseEnd_7411728] using wordTrace_append hprefix tailTrace_7411728
  have hstable : (prefixWord ++ tailWord_7411728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7411728).length < 2 ^ (prefixWord ++ tailWord_7411728).sum := by decide
  have hdescent : baseEnd_7411728 < baseStart_7411728 := by decide
  rcases family_descends (prefixWord ++ tailWord_7411728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7411766 : List Nat := [5, 1, 2, 1, 1, 1, 4, 2, 2, 1, 3]
def baseStart_7411766 : Nat := 118140960795 + 7411766 * 2 ^ 59
def prefixEnd_7411766 : Nat := 4983230072969 + 3 ^ 40 * 7411766 * 2
def baseEnd_7411766 : Nat := 3805798456651953665138915

theorem tailTrace_7411766 : CollatzResearch.WordTrace tailWord_7411766 prefixEnd_7411766 3805798456651953665138915 := by
  unfold tailWord_7411766
  simp only [CollatzResearch.WordTrace]
  refine ⟨16895582154152817856257947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 180219542977630057133418101 16895582154152817856257947)
  ·
    refine ⟨25343373231229226784386921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16895582154152817856257947 25343373231229226784386921)
    ·
      refine ⟨19007529923421920088290191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25343373231229226784386921 19007529923421920088290191)
      ·
        refine ⟨28511294885132880132435287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19007529923421920088290191 28511294885132880132435287)
        ·
          refine ⟨42766942327699320198652931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28511294885132880132435287 42766942327699320198652931)
          ·
            refine ⟨64150413491548980297979397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42766942327699320198652931 64150413491548980297979397)
            ·
              refine ⟨12028202529665433805871137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 64150413491548980297979397 12028202529665433805871137)
              ·
                refine ⟨9021151897249075354403353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12028202529665433805871137 9021151897249075354403353)
                ·
                  refine ⟨6765863922936806515802515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9021151897249075354403353 6765863922936806515802515)
                  ·
                    refine ⟨10148795884405209773703773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6765863922936806515802515 10148795884405209773703773)
                    ·
                      refine ⟨3805798456651953665138915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10148795884405209773703773 3805798456651953665138915)
                      ·
                        rfl

theorem cell23_7411766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 4, 2, 2, 1, 3].length) (baseStart_7411766 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7411766 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7411766 prefixEnd_7411766 := by exact prefixLift 7411766
  have htrace : WordTrace (prefixWord ++ tailWord_7411766) baseStart_7411766 baseEnd_7411766 := by
    simpa [prefixWord, tailWord_7411766, baseEnd_7411766] using wordTrace_append hprefix tailTrace_7411766
  have hstable : (prefixWord ++ tailWord_7411766).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7411766).length < 2 ^ (prefixWord ++ tailWord_7411766).sum := by decide
  have hdescent : baseEnd_7411766 < baseStart_7411766 := by decide
  rcases family_descends (prefixWord ++ tailWord_7411766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7411772 : List Nat := [2, 2, 2, 2, 2, 1, 1, 2, 3, 4, 2]
def baseStart_7411772 : Nat := 118140960795 + 7411772 * 2 ^ 59
def prefixEnd_7411772 : Nat := 4983230072969 + 3 ^ 40 * 7411772 * 2
def baseEnd_7411772 : Nat := 3805801537535880641663887

theorem tailTrace_7411772 : CollatzResearch.WordTrace tailWord_7411772 prefixEnd_7411772 3805801537535880641663887 := by
  unfold tailWord_7411772
  simp only [CollatzResearch.WordTrace]
  refine ⟨135164766652211674362422785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180219688869615565816563713 135164766652211674362422785)
  ·
    refine ⟨101373574989158755771817089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135164766652211674362422785 101373574989158755771817089)
    ·
      refine ⟨76030181241869066828862817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101373574989158755771817089 76030181241869066828862817)
      ·
        refine ⟨57022635931401800121647113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76030181241869066828862817 57022635931401800121647113)
        ·
          refine ⟨42766976948551350091235335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57022635931401800121647113 42766976948551350091235335)
          ·
            refine ⟨64150465422827025136853003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42766976948551350091235335 64150465422827025136853003)
            ·
              refine ⟨96225698134240537705279505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64150465422827025136853003 96225698134240537705279505)
              ·
                refine ⟨72169273600680403278959629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 96225698134240537705279505 72169273600680403278959629)
                ·
                  refine ⟨27063477600255151229609861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 72169273600680403278959629 27063477600255151229609861)
                  ·
                    refine ⟨5074402050047840855551849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27063477600255151229609861 5074402050047840855551849)
                    ·
                      refine ⟨3805801537535880641663887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5074402050047840855551849 3805801537535880641663887)
                      ·
                        rfl

theorem cell23_7411772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 2, 3, 4, 2].length) (baseStart_7411772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7411772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7411772 prefixEnd_7411772 := by exact prefixLift 7411772
  have htrace : WordTrace (prefixWord ++ tailWord_7411772) baseStart_7411772 baseEnd_7411772 := by
    simpa [prefixWord, tailWord_7411772, baseEnd_7411772] using wordTrace_append hprefix tailTrace_7411772
  have hstable : (prefixWord ++ tailWord_7411772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7411772).length < 2 ^ (prefixWord ++ tailWord_7411772).sum := by decide
  have hdescent : baseEnd_7411772 < baseStart_7411772 := by decide
  rcases family_descends (prefixWord ++ tailWord_7411772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7411775 : List Nat := [1, 1, 2, 2, 3, 1, 3, 1, 2, 4, 3]
def baseStart_7411775 : Nat := 118140960795 + 7411775 * 2 ^ 59
def prefixEnd_7411775 : Nat := 4983230072969 + 3 ^ 40 * 7411775 * 2
def baseEnd_7411775 : Nat := 3805803077977844129926373

theorem tailTrace_7411775 : CollatzResearch.WordTrace tailWord_7411775 prefixEnd_7411775 3805803077977844129926373 := by
  unfold tailWord_7411775
  simp only [CollatzResearch.WordTrace]
  refine ⟨270329642723412480237204779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180219761815608320158136519 270329642723412480237204779)
  ·
    refine ⟨405494464085118720355807169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270329642723412480237204779 405494464085118720355807169)
    ·
      refine ⟨304120848063839040266855377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 405494464085118720355807169 304120848063839040266855377)
      ·
        refine ⟨228090636047879280200141533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 304120848063839040266855377 228090636047879280200141533)
        ·
          refine ⟨85533988517954730075053075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 228090636047879280200141533 85533988517954730075053075)
          ·
            refine ⟨128300982776932095112579613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85533988517954730075053075 128300982776932095112579613)
            ·
              refine ⟨48112868541349535667217355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 128300982776932095112579613 48112868541349535667217355)
              ·
                refine ⟨72169302812024303500826033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48112868541349535667217355 72169302812024303500826033)
                ·
                  refine ⟨54126977109018227625619525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 72169302812024303500826033 54126977109018227625619525)
                  ·
                    refine ⟨10148808207940917679803661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 54126977109018227625619525 10148808207940917679803661)
                    ·
                      refine ⟨3805803077977844129926373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10148808207940917679803661 3805803077977844129926373)
                      ·
                        rfl

theorem cell23_7411775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 3, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 3, 1, 2, 4, 3].length) (baseStart_7411775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7411775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7411775 prefixEnd_7411775 := by exact prefixLift 7411775
  have htrace : WordTrace (prefixWord ++ tailWord_7411775) baseStart_7411775 baseEnd_7411775 := by
    simpa [prefixWord, tailWord_7411775, baseEnd_7411775] using wordTrace_append hprefix tailTrace_7411775
  have hstable : (prefixWord ++ tailWord_7411775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7411775).length < 2 ^ (prefixWord ++ tailWord_7411775).sum := by decide
  have hdescent : baseEnd_7411775 < baseStart_7411775 := by decide
  rcases family_descends (prefixWord ++ tailWord_7411775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7411785 : List Nat := [1, 2, 1, 1, 2, 2, 5, 1, 2, 2, 4]
def baseStart_7411785 : Nat := 118140960795 + 7411785 * 2 ^ 59
def prefixEnd_7411785 : Nat := 4983230072969 + 3 ^ 40 * 7411785 * 2
def baseEnd_7411785 : Nat := 3805808212784389090801327

theorem tailTrace_7411785 : CollatzResearch.WordTrace tailWord_7411785 prefixEnd_7411785 3805808212784389090801327 := by
  unfold tailWord_7411785
  simp only [CollatzResearch.WordTrace]
  refine ⟨270330007453376251945068809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180220004968917501296712539 270330007453376251945068809)
  ·
    refine ⟨202747505590032188958801607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 270330007453376251945068809 202747505590032188958801607)
    ·
      refine ⟨304121258385048283438202411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202747505590032188958801607 304121258385048283438202411)
      ·
        refine ⟨456181887577572425157303617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 304121258385048283438202411 456181887577572425157303617)
        ·
          refine ⟨342136415683179318867977713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 456181887577572425157303617 342136415683179318867977713)
          ·
            refine ⟨256602311762384489150983285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 342136415683179318867977713 256602311762384489150983285)
            ·
              refine ⟨24056466727723545857904683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 256602311762384489150983285 24056466727723545857904683)
              ·
                refine ⟨36084700091585318786857025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24056466727723545857904683 36084700091585318786857025)
                ·
                  refine ⟨27063525068688989090142769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36084700091585318786857025 27063525068688989090142769)
                  ·
                    refine ⟨20297643801516741817607077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27063525068688989090142769 20297643801516741817607077)
                    ·
                      refine ⟨3805808212784389090801327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20297643801516741817607077 3805808212784389090801327)
                      ·
                        rfl

theorem cell23_7411785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 5, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 5, 1, 2, 2, 4].length) (baseStart_7411785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7411785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7411785 prefixEnd_7411785 := by exact prefixLift 7411785
  have htrace : WordTrace (prefixWord ++ tailWord_7411785) baseStart_7411785 baseEnd_7411785 := by
    simpa [prefixWord, tailWord_7411785, baseEnd_7411785] using wordTrace_append hprefix tailTrace_7411785
  have hstable : (prefixWord ++ tailWord_7411785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7411785).length < 2 ^ (prefixWord ++ tailWord_7411785).sum := by decide
  have hdescent : baseEnd_7411785 < baseStart_7411785 := by decide
  rcases family_descends (prefixWord ++ tailWord_7411785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7411810 : List Nat := [3, 3, 2, 2, 2, 2, 2, 1, 1, 3, 2]
def baseStart_7411810 : Nat := 118140960795 + 7411810 * 2 ^ 59
def prefixEnd_7411810 : Nat := 4983230072969 + 3 ^ 40 * 7411810 * 2
def baseEnd_7411810 : Nat := 3805821049800751492988713

theorem tailTrace_7411810 : CollatzResearch.WordTrace tailWord_7411810 prefixEnd_7411810 3805821049800751492988713 := by
  unfold tailWord_7411810
  simp only [CollatzResearch.WordTrace]
  refine ⟨67582729819571420303682221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 180220612852190454143152589 67582729819571420303682221)
  ·
    refine ⟨25343523682339282613880833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67582729819571420303682221 25343523682339282613880833)
    ·
      refine ⟨19007642761754461960410625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25343523682339282613880833 19007642761754461960410625)
      ·
        refine ⟨14255732071315846470307969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19007642761754461960410625 14255732071315846470307969)
        ·
          refine ⟨10691799053486884852730977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14255732071315846470307969 10691799053486884852730977)
          ·
            refine ⟨8018849290115163639548233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10691799053486884852730977 8018849290115163639548233)
            ·
              refine ⟨6014136967586372729661175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8018849290115163639548233 6014136967586372729661175)
              ·
                refine ⟨9021205451379559094491763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6014136967586372729661175 9021205451379559094491763)
                ·
                  refine ⟨13531808177069338641737645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9021205451379559094491763 13531808177069338641737645)
                  ·
                    refine ⟨5074428066401001990651617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13531808177069338641737645 5074428066401001990651617)
                    ·
                      refine ⟨3805821049800751492988713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5074428066401001990651617 3805821049800751492988713)
                      ·
                        rfl

theorem cell23_7411810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 2, 2, 1, 1, 3, 2].length) (baseStart_7411810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7411810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7411810 prefixEnd_7411810 := by exact prefixLift 7411810
  have htrace : WordTrace (prefixWord ++ tailWord_7411810) baseStart_7411810 baseEnd_7411810 := by
    simpa [prefixWord, tailWord_7411810, baseEnd_7411810] using wordTrace_append hprefix tailTrace_7411810
  have hstable : (prefixWord ++ tailWord_7411810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7411810).length < 2 ^ (prefixWord ++ tailWord_7411810).sum := by decide
  have hdescent : baseEnd_7411810 < baseStart_7411810 := by decide
  rcases family_descends (prefixWord ++ tailWord_7411810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7411812 : List Nat := [2, 3, 1, 1, 2, 1, 3, 5, 5]
def baseStart_7411812 : Nat := 118140960795 + 7411812 * 2 ^ 59
def prefixEnd_7411812 : Nat := 4983230072969 + 3 ^ 40 * 7411812 * 2
def baseEnd_7411812 : Nat := 422869119640228942795967

theorem tailTrace_7411812 : CollatzResearch.WordTrace tailWord_7411812 prefixEnd_7411812 422869119640228942795967 := by
  unfold tailWord_7411812
  simp only [CollatzResearch.WordTrace]
  refine ⟨135165496112139217778150845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180220661482852290370867793 135165496112139217778150845)
  ·
    refine ⟨50687061042052206666806567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 135165496112139217778150845 50687061042052206666806567)
    ·
      refine ⟨76030591563078310000209851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50687061042052206666806567 76030591563078310000209851)
      ·
        refine ⟨114045887344617465000314777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76030591563078310000209851 114045887344617465000314777)
        ·
          refine ⟨85534415508463098750236083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114045887344617465000314777 85534415508463098750236083)
          ·
            refine ⟨128301623262694648125354125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85534415508463098750236083 128301623262694648125354125)
            ·
              refine ⟨48113108723510493047007797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 128301623262694648125354125 48113108723510493047007797)
              ·
                refine ⟨4510603942829108723156981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 48113108723510493047007797 4510603942829108723156981)
                ·
                  refine ⟨422869119640228942795967, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4510603942829108723156981 422869119640228942795967)
                  ·
                    rfl

theorem cell23_7411812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 3, 5, 5].length) (baseStart_7411812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7411812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7411812 prefixEnd_7411812 := by exact prefixLift 7411812
  have htrace : WordTrace (prefixWord ++ tailWord_7411812) baseStart_7411812 baseEnd_7411812 := by
    simpa [prefixWord, tailWord_7411812, baseEnd_7411812] using wordTrace_append hprefix tailTrace_7411812
  have hstable : (prefixWord ++ tailWord_7411812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7411812).length < 2 ^ (prefixWord ++ tailWord_7411812).sum := by decide
  have hdescent : baseEnd_7411812 < baseStart_7411812 := by decide
  rcases family_descends (prefixWord ++ tailWord_7411812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7411822 : List Nat := [4, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3]
def baseStart_7411822 : Nat := 118140960795 + 7411822 * 2 ^ 59
def prefixEnd_7411822 : Nat := 4983230072969 + 3 ^ 40 * 7411822 * 2
def baseEnd_7411822 : Nat := 3805827211568605446038657

theorem tailTrace_7411822 : CollatzResearch.WordTrace tailWord_7411822 prefixEnd_7411822 3805827211568605446038657 := by
  unfold tailWord_7411822
  simp only [CollatzResearch.WordTrace]
  refine ⟨33791419619280275908020715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 180220904636161471509443813 33791419619280275908020715)
  ·
    refine ⟨50687129428920413862031073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33791419619280275908020715 50687129428920413862031073)
    ·
      refine ⟨38015347071690310396523305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50687129428920413862031073 38015347071690310396523305)
      ·
        refine ⟨28511510303767732797392479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38015347071690310396523305 28511510303767732797392479)
        ·
          refine ⟨42767265455651599196088719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28511510303767732797392479 42767265455651599196088719)
          ·
            refine ⟨64150898183477398794133079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42767265455651599196088719 64150898183477398794133079)
            ·
              refine ⟨96226347275216098191199619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64150898183477398794133079 96226347275216098191199619)
              ·
                refine ⟨144339520912824147286799429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 96226347275216098191199619 144339520912824147286799429)
                ·
                  refine ⟨27063660171154527616274893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 144339520912824147286799429 27063660171154527616274893)
                  ·
                    refine ⟨10148872564182947856103085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27063660171154527616274893 10148872564182947856103085)
                    ·
                      refine ⟨3805827211568605446038657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10148872564182947856103085 3805827211568605446038657)
                      ·
                        rfl

theorem cell23_7411822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3].length) (baseStart_7411822 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7411822 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7411822 prefixEnd_7411822 := by exact prefixLift 7411822
  have htrace : WordTrace (prefixWord ++ tailWord_7411822) baseStart_7411822 baseEnd_7411822 := by
    simpa [prefixWord, tailWord_7411822, baseEnd_7411822] using wordTrace_append hprefix tailTrace_7411822
  have hstable : (prefixWord ++ tailWord_7411822).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7411822).length < 2 ^ (prefixWord ++ tailWord_7411822).sum := by decide
  have hdescent : baseEnd_7411822 < baseStart_7411822 := by decide
  rcases family_descends (prefixWord ++ tailWord_7411822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7411825 : List Nat := [1, 2, 2, 2, 1, 1, 4, 1, 4, 5]
def baseStart_7411825 : Nat := 118140960795 + 7411825 * 2 ^ 59
def prefixEnd_7411825 : Nat := 4983230072969 + 3 ^ 40 * 7411825 * 2
def baseEnd_7411825 : Nat := 1268609584003522978100381

theorem tailTrace_7411825 : CollatzResearch.WordTrace tailWord_7411825 prefixEnd_7411825 1268609584003522978100381 := by
  unfold tailWord_7411825
  simp only [CollatzResearch.WordTrace]
  refine ⟨270331466373231338776524929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180220977582154225851016619 270331466373231338776524929)
  ·
    refine ⟨202748599779923504082393697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 270331466373231338776524929 202748599779923504082393697)
    ·
      refine ⟨152061449834942628061795273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 202748599779923504082393697 152061449834942628061795273)
      ·
        refine ⟨114046087376206971046346455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 152061449834942628061795273 114046087376206971046346455)
        ·
          refine ⟨171069131064310456569519683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114046087376206971046346455 171069131064310456569519683)
          ·
            refine ⟨256603696596465684854279525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 171069131064310456569519683 256603696596465684854279525)
            ·
              refine ⟨48113193111837315910177411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 256603696596465684854279525 48113193111837315910177411)
              ·
                refine ⟨72169789667755973865266117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48113193111837315910177411 72169789667755973865266117)
                ·
                  refine ⟨13531835562704245099737397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 72169789667755973865266117 13531835562704245099737397)
                  ·
                    refine ⟨1268609584003522978100381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13531835562704245099737397 1268609584003522978100381)
                    ·
                      rfl

theorem cell23_7411825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 4, 1, 4, 5].length) (baseStart_7411825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7411825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7411825 prefixEnd_7411825 := by exact prefixLift 7411825
  have htrace : WordTrace (prefixWord ++ tailWord_7411825) baseStart_7411825 baseEnd_7411825 := by
    simpa [prefixWord, tailWord_7411825, baseEnd_7411825] using wordTrace_append hprefix tailTrace_7411825
  have hstable : (prefixWord ++ tailWord_7411825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7411825).length < 2 ^ (prefixWord ++ tailWord_7411825).sum := by decide
  have hdescent : baseEnd_7411825 < baseStart_7411825 := by decide
  rcases family_descends (prefixWord ++ tailWord_7411825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7411886 : List Nat := [4, 1, 4, 2, 1, 1, 1, 1, 1, 2, 5]
def baseStart_7411886 : Nat := 118140960795 + 7411886 * 2 ^ 59
def prefixEnd_7411886 : Nat := 4983230072969 + 3 ^ 40 * 7411886 * 2
def baseEnd_7411886 : Nat := 3805860074330493195638363

theorem tailTrace_7411886 : CollatzResearch.WordTrace tailWord_7411886 prefixEnd_7411886 3805860074330493195638363 := by
  unfold tailWord_7411886
  simp only [CollatzResearch.WordTrace]
  refine ⟨33791711403251293274311939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 180222460817340230796330341 33791711403251293274311939)
  ·
    refine ⟨50687567104876939911467909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33791711403251293274311939 50687567104876939911467909)
    ·
      refine ⟨9503918832164426233400233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 50687567104876939911467909 9503918832164426233400233)
      ·
        refine ⟨7127939124123319675050175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9503918832164426233400233 7127939124123319675050175)
        ·
          refine ⟨10691908686184979512575263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7127939124123319675050175 10691908686184979512575263)
          ·
            refine ⟨16037863029277469268862895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10691908686184979512575263 16037863029277469268862895)
            ·
              refine ⟨24056794543916203903294343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16037863029277469268862895 24056794543916203903294343)
              ·
                refine ⟨36085191815874305854941515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24056794543916203903294343 36085191815874305854941515)
                ·
                  refine ⟨54127787723811458782412273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36085191815874305854941515 54127787723811458782412273)
                  ·
                    refine ⟨40595840792858594086809205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 54127787723811458782412273 40595840792858594086809205)
                    ·
                      refine ⟨3805860074330493195638363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40595840792858594086809205 3805860074330493195638363)
                      ·
                        rfl

theorem cell23_7411886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 1, 1, 1, 2, 5].length) (baseStart_7411886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7411886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7411886 prefixEnd_7411886 := by exact prefixLift 7411886
  have htrace : WordTrace (prefixWord ++ tailWord_7411886) baseStart_7411886 baseEnd_7411886 := by
    simpa [prefixWord, tailWord_7411886, baseEnd_7411886] using wordTrace_append hprefix tailTrace_7411886
  have hstable : (prefixWord ++ tailWord_7411886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7411886).length < 2 ^ (prefixWord ++ tailWord_7411886).sum := by decide
  have hdescent : baseEnd_7411886 < baseStart_7411886 := by decide
  rcases family_descends (prefixWord ++ tailWord_7411886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7411962 : List Nat := [3, 1, 1, 1, 1, 5, 1, 3, 1, 6]
def baseStart_7411962 : Nat := 118140960795 + 7411962 * 2 ^ 59
def prefixEnd_7411962 : Nat := 4983230072969 + 3 ^ 40 * 7411962 * 2
def baseEnd_7411962 : Nat := 1268633032953411632762671

theorem tailTrace_7411962 : CollatzResearch.WordTrace tailWord_7411962 prefixEnd_7411962 1268633032953411632762671 := by
  unfold tailWord_7411962
  simp only [CollatzResearch.WordTrace]
  refine ⟨67584115793433752793565535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 180224308782490007449508093 67584115793433752793565535)
  ·
    refine ⟨101376173690150629190348303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67584115793433752793565535 101376173690150629190348303)
    ·
      refine ⟨152064260535225943785522455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101376173690150629190348303 152064260535225943785522455)
      ·
        refine ⟨228096390802838915678283683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152064260535225943785522455 228096390802838915678283683)
        ·
          refine ⟨342144586204258373517425525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 228096390802838915678283683 342144586204258373517425525)
          ·
            refine ⟨32076054956649222517258643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 342144586204258373517425525 32076054956649222517258643)
            ·
              refine ⟨48114082434973833775887965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32076054956649222517258643 48114082434973833775887965)
              ·
                refine ⟨18042780913115187665957987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48114082434973833775887965 18042780913115187665957987)
                ·
                  refine ⟨27064171369672781498936981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18042780913115187665957987 27064171369672781498936981)
                  ·
                    refine ⟨1268633032953411632762671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27064171369672781498936981 1268633032953411632762671)
                    ·
                      rfl

theorem cell23_7411962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 1, 3, 1, 6].length) (baseStart_7411962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7411962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7411962 prefixEnd_7411962 := by exact prefixLift 7411962
  have htrace : WordTrace (prefixWord ++ tailWord_7411962) baseStart_7411962 baseEnd_7411962 := by
    simpa [prefixWord, tailWord_7411962, baseEnd_7411962] using wordTrace_append hprefix tailTrace_7411962
  have hstable : (prefixWord ++ tailWord_7411962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7411962).length < 2 ^ (prefixWord ++ tailWord_7411962).sum := by decide
  have hdescent : baseEnd_7411962 < baseStart_7411962 := by decide
  rcases family_descends (prefixWord ++ tailWord_7411962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7411969 : List Nat := [1, 2, 4, 1, 1, 2, 2, 4, 1, 1, 4]
def baseStart_7411969 : Nat := 118140960795 + 7411969 * 2 ^ 59
def prefixEnd_7411969 : Nat := 4983230072969 + 3 ^ 40 * 7411969 * 2
def baseEnd_7411969 : Nat := 3805902693224816370900481

theorem tailTrace_7411969 : CollatzResearch.WordTrace tailWord_7411969 prefixEnd_7411969 3805902693224816370900481 := by
  unfold tailWord_7411969
  simp only [CollatzResearch.WordTrace]
  refine ⟨270336718484709651369766961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180224478989806434246511307 270336718484709651369766961)
  ·
    refine ⟨202752538863532238527325221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 270336718484709651369766961 202752538863532238527325221)
    ·
      refine ⟨38016101036912294723873479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 202752538863532238527325221 38016101036912294723873479)
      ·
        refine ⟨57024151555368442085810219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38016101036912294723873479 57024151555368442085810219)
        ·
          refine ⟨85536227333052663128715329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57024151555368442085810219 85536227333052663128715329)
          ·
            refine ⟨64152170499789497346536497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85536227333052663128715329 64152170499789497346536497)
            ·
              refine ⟨48114127874842123009902373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64152170499789497346536497 48114127874842123009902373)
              ·
                refine ⟨9021398976532898064356695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48114127874842123009902373 9021398976532898064356695)
                ·
                  refine ⟨13532098464799347096535043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9021398976532898064356695 13532098464799347096535043)
                  ·
                    refine ⟨20298147697199020644802565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13532098464799347096535043 20298147697199020644802565)
                    ·
                      refine ⟨3805902693224816370900481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20298147697199020644802565 3805902693224816370900481)
                      ·
                        rfl

theorem cell23_7411969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 2, 4, 1, 1, 4].length) (baseStart_7411969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7411969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7411969 prefixEnd_7411969 := by exact prefixLift 7411969
  have htrace : WordTrace (prefixWord ++ tailWord_7411969) baseStart_7411969 baseEnd_7411969 := by
    simpa [prefixWord, tailWord_7411969, baseEnd_7411969] using wordTrace_append hprefix tailTrace_7411969
  have hstable : (prefixWord ++ tailWord_7411969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7411969).length < 2 ^ (prefixWord ++ tailWord_7411969).sum := by decide
  have hdescent : baseEnd_7411969 < baseStart_7411969 := by decide
  rcases family_descends (prefixWord ++ tailWord_7411969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7412003 : List Nat := [1, 1, 1, 4, 2, 2, 1, 6, 1, 2, 2]
def baseStart_7412003 : Nat := 118140960795 + 7412003 * 2 ^ 59
def prefixEnd_7412003 : Nat := 4983230072969 + 3 ^ 40 * 7412003 * 2
def baseEnd_7412003 : Nat := 3805920151567069237875325

theorem tailTrace_7412003 : CollatzResearch.WordTrace tailWord_7412003 prefixEnd_7412003 3805920151567069237875325 := by
  unfold tailWord_7412003
  simp only [CollatzResearch.WordTrace]
  refine ⟨270337958566586475176504663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180225305711057650117669775 270337958566586475176504663)
  ·
    refine ⟨405506937849879712764756995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270337958566586475176504663 405506937849879712764756995)
    ·
      refine ⟨608260406774819569147135493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 405506937849879712764756995 608260406774819569147135493)
      ·
        refine ⟨114048826270278669215087905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 608260406774819569147135493 114048826270278669215087905)
        ·
          refine ⟨85536619702709001911315929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114048826270278669215087905 85536619702709001911315929)
          ·
            refine ⟨64152464777031751433486947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85536619702709001911315929 64152464777031751433486947)
            ·
              refine ⟨96228697165547627150230421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64152464777031751433486947 96228697165547627150230421)
              ·
                refine ⟨4510720179635045022667051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 96228697165547627150230421 4510720179635045022667051)
                ·
                  refine ⟨6766080269452567534000577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4510720179635045022667051 6766080269452567534000577)
                  ·
                    refine ⟨5074560202089425650500433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6766080269452567534000577 5074560202089425650500433)
                    ·
                      refine ⟨3805920151567069237875325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5074560202089425650500433 3805920151567069237875325)
                      ·
                        rfl

theorem cell23_7412003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 6, 1, 2, 2].length) (baseStart_7412003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7412003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7412003 prefixEnd_7412003 := by exact prefixLift 7412003
  have htrace : WordTrace (prefixWord ++ tailWord_7412003) baseStart_7412003 baseEnd_7412003 := by
    simpa [prefixWord, tailWord_7412003, baseEnd_7412003] using wordTrace_append hprefix tailTrace_7412003
  have hstable : (prefixWord ++ tailWord_7412003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7412003).length < 2 ^ (prefixWord ++ tailWord_7412003).sum := by decide
  have hdescent : baseEnd_7412003 < baseStart_7412003 := by decide
  rcases family_descends (prefixWord ++ tailWord_7412003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7412013 : List Nat := [1, 5, 3, 1, 2, 2, 1, 1, 1, 6]
def baseStart_7412013 : Nat := 118140960795 + 7412013 * 2 ^ 59
def prefixEnd_7412013 : Nat := 4983230072969 + 3 ^ 40 * 7412013 * 2
def baseEnd_7412013 : Nat := 1268641762124538066250093

theorem tailTrace_7412013 : CollatzResearch.WordTrace tailWord_7412013 prefixEnd_7412013 1268641762124538066250093 := by
  unfold tailWord_7412013
  simp only [CollatzResearch.WordTrace]
  refine ⟨270338323296550246884368693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180225548864366831256245795 270338323296550246884368693)
  ·
    refine ⟨25344217809051585645409565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 270338323296550246884368693 25344217809051585645409565)
    ·
      refine ⟨9504081678394344617028587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25344217809051585645409565 9504081678394344617028587)
      ·
        refine ⟨14256122517591516925542881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9504081678394344617028587 14256122517591516925542881)
        ·
          refine ⟨10692091888193637694157161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14256122517591516925542881 10692091888193637694157161)
          ·
            refine ⟨8019068916145228270617871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10692091888193637694157161 8019068916145228270617871)
            ·
              refine ⟨12028603374217842405926807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8019068916145228270617871 12028603374217842405926807)
              ·
                refine ⟨18042905061326763608890211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12028603374217842405926807 18042905061326763608890211)
                ·
                  refine ⟨27064357591990145413335317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18042905061326763608890211 27064357591990145413335317)
                  ·
                    refine ⟨1268641762124538066250093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27064357591990145413335317 1268641762124538066250093)
                    ·
                      rfl

theorem cell23_7412013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 2, 1, 1, 1, 6].length) (baseStart_7412013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7412013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7412013 prefixEnd_7412013 := by exact prefixLift 7412013
  have htrace : WordTrace (prefixWord ++ tailWord_7412013) baseStart_7412013 baseEnd_7412013 := by
    simpa [prefixWord, tailWord_7412013, baseEnd_7412013] using wordTrace_append hprefix tailTrace_7412013
  have hstable : (prefixWord ++ tailWord_7412013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7412013).length < 2 ^ (prefixWord ++ tailWord_7412013).sum := by decide
  have hdescent : baseEnd_7412013 < baseStart_7412013 := by decide
  rcases family_descends (prefixWord ++ tailWord_7412013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7412042 : List Nat := [3, 1, 2, 1, 1, 1, 1, 1, 3, 5, 4]
def baseStart_7412042 : Nat := 118140960795 + 7412042 * 2 ^ 59
def prefixEnd_7412042 : Nat := 4983230072969 + 3 ^ 40 * 7412042 * 2
def baseEnd_7412042 : Nat := 3805940177312594585287645

theorem tailTrace_7412042 : CollatzResearch.WordTrace tailWord_7412042 prefixEnd_7412042 3805940177312594585287645 := by
  unfold tailWord_7412042
  simp only [CollatzResearch.WordTrace]
  refine ⟨67584845253361296209293595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 180226254008963456558116253 67584845253361296209293595)
  ·
    refine ⟨101377267880041944313940393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67584845253361296209293595 101377267880041944313940393)
    ·
      refine ⟨76032950910031458235455295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101377267880041944313940393 76032950910031458235455295)
      ·
        refine ⟨114049426365047187353182943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76032950910031458235455295 114049426365047187353182943)
        ·
          refine ⟨171074139547570781029774415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114049426365047187353182943 171074139547570781029774415)
          ·
            refine ⟨256611209321356171544661623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 171074139547570781029774415 256611209321356171544661623)
            ·
              refine ⟨384916813982034257316992435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 256611209321356171544661623 384916813982034257316992435)
              ·
                refine ⟨577375220973051385975488653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 384916813982034257316992435 577375220973051385975488653)
                ·
                  refine ⟨216515707864894269740808245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 577375220973051385975488653 216515707864894269740808245)
                  ·
                    refine ⟨20298347612333837788200773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 216515707864894269740808245 20298347612333837788200773)
                    ·
                      refine ⟨3805940177312594585287645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20298347612333837788200773 3805940177312594585287645)
                      ·
                        rfl

theorem cell23_7412042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 5, 4].length) (baseStart_7412042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7412042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7412042 prefixEnd_7412042 := by exact prefixLift 7412042
  have htrace : WordTrace (prefixWord ++ tailWord_7412042) baseStart_7412042 baseEnd_7412042 := by
    simpa [prefixWord, tailWord_7412042, baseEnd_7412042] using wordTrace_append hprefix tailTrace_7412042
  have hstable : (prefixWord ++ tailWord_7412042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7412042).length < 2 ^ (prefixWord ++ tailWord_7412042).sum := by decide
  have hdescent : baseEnd_7412042 < baseStart_7412042 := by decide
  rcases family_descends (prefixWord ++ tailWord_7412042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7412092 : List Nat := [2, 2, 2, 1, 1, 1, 2, 2, 1, 2, 7]
def baseStart_7412092 : Nat := 118140960795 + 7412092 * 2 ^ 59
def prefixEnd_7412092 : Nat := 4983230072969 + 3 ^ 40 * 7412092 * 2
def baseEnd_7412092 : Nat := 3805965851345319389662415

theorem tailTrace_7412092 : CollatzResearch.WordTrace tailWord_7412092 prefixEnd_7412092 3805965851345319389662415 := by
  unfold tailWord_7412092
  simp only [CollatzResearch.WordTrace]
  refine ⟨135170602331632021688247265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180227469775509362250996353 135170602331632021688247265)
  ·
    refine ⟨101377951748724016266185449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135170602331632021688247265 101377951748724016266185449)
    ·
      refine ⟨76033463811543012199639087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101377951748724016266185449 76033463811543012199639087)
      ·
        refine ⟨114050195717314518299458631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76033463811543012199639087 114050195717314518299458631)
        ·
          refine ⟨171075293575971777449187947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114050195717314518299458631 171075293575971777449187947)
          ·
            refine ⟨256612940363957666173781921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 171075293575971777449187947 256612940363957666173781921)
            ·
              refine ⟨192459705272968249630336441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 256612940363957666173781921 192459705272968249630336441)
              ·
                refine ⟨144344778954726187222752331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 192459705272968249630336441 144344778954726187222752331)
                ·
                  refine ⟨216517168432089280834128497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 144344778954726187222752331 216517168432089280834128497)
                  ·
                    refine ⟨162387876324066960625596373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 216517168432089280834128497 162387876324066960625596373)
                    ·
                      refine ⟨3805965851345319389662415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 162387876324066960625596373 3805965851345319389662415)
                      ·
                        rfl

theorem cell23_7412092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 2, 1, 2, 7].length) (baseStart_7412092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7412092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7412092 prefixEnd_7412092 := by exact prefixLift 7412092
  have htrace : WordTrace (prefixWord ++ tailWord_7412092) baseStart_7412092 baseEnd_7412092 := by
    simpa [prefixWord, tailWord_7412092, baseEnd_7412092] using wordTrace_append hprefix tailTrace_7412092
  have hstable : (prefixWord ++ tailWord_7412092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7412092).length < 2 ^ (prefixWord ++ tailWord_7412092).sum := by decide
  have hdescent : baseEnd_7412092 < baseStart_7412092 := by decide
  rcases family_descends (prefixWord ++ tailWord_7412092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7412110 : List Nat := [4, 1, 1, 4, 1, 1, 1, 4, 2, 2, 2]
def baseStart_7412110 : Nat := 118140960795 + 7412110 * 2 ^ 59
def prefixEnd_7412110 : Nat := 4983230072969 + 3 ^ 40 * 7412110 * 2
def baseEnd_7412110 : Nat := 3805975093997100319237333

theorem tailTrace_7412110 : CollatzResearch.WordTrace tailWord_7412110 prefixEnd_7412110 3805975093997100319237333 := by
  unfold tailWord_7412110
  simp only [CollatzResearch.WordTrace]
  refine ⟨33792732647149854056331223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 180227907451465888300433189 33792732647149854056331223)
  ·
    refine ⟨50689098970724781084496835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33792732647149854056331223 50689098970724781084496835)
    ·
      refine ⟨76033648456087171626745253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50689098970724781084496835 76033648456087171626745253)
      ·
        refine ⟨14256309085516344680014735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 76033648456087171626745253 14256309085516344680014735)
        ·
          refine ⟨21384463628274517020022103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14256309085516344680014735 21384463628274517020022103)
          ·
            refine ⟨32076695442411775530033155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21384463628274517020022103 32076695442411775530033155)
            ·
              refine ⟨48115043163617663295049733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32076695442411775530033155 48115043163617663295049733)
              ·
                refine ⟨9021570593178311867821825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48115043163617663295049733 9021570593178311867821825)
                ·
                  refine ⟨6766177944883733900866369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9021570593178311867821825 6766177944883733900866369)
                  ·
                    refine ⟨5074633458662800425649777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6766177944883733900866369 5074633458662800425649777)
                    ·
                      refine ⟨3805975093997100319237333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5074633458662800425649777 3805975093997100319237333)
                      ·
                        rfl

theorem cell23_7412110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 1, 4, 2, 2, 2].length) (baseStart_7412110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7412110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7412110 prefixEnd_7412110 := by exact prefixLift 7412110
  have htrace : WordTrace (prefixWord ++ tailWord_7412110) baseStart_7412110 baseEnd_7412110 := by
    simpa [prefixWord, tailWord_7412110, baseEnd_7412110] using wordTrace_append hprefix tailTrace_7412110
  have hstable : (prefixWord ++ tailWord_7412110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7412110).length < 2 ^ (prefixWord ++ tailWord_7412110).sum := by decide
  have hdescent : baseEnd_7412110 < baseStart_7412110 := by decide
  rcases family_descends (prefixWord ++ tailWord_7412110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7412161 : List Nat := [1, 2, 7, 1, 1, 2, 1, 2, 2, 2, 2]
def baseStart_7412161 : Nat := 118140960795 + 7412161 * 2 ^ 59
def prefixEnd_7412161 : Nat := 4983230072969 + 3 ^ 40 * 7412161 * 2
def baseEnd_7412161 : Nat := 3806001281510479619699599

theorem tailTrace_7412161 : CollatzResearch.WordTrace tailWord_7412161 prefixEnd_7412161 3806001281510479619699599 := by
  unfold tailWord_7412161
  simp only [CollatzResearch.WordTrace]
  refine ⟨270343721300014068160756337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180229147533342712107170891 270343721300014068160756337)
  ·
    refine ⟨202757790975010551120567253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 270343721300014068160756337 202757790975010551120567253)
    ·
      refine ⟨4752135725976809791888295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 202757790975010551120567253 4752135725976809791888295)
      ·
        refine ⟨7128203588965214687832443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4752135725976809791888295 7128203588965214687832443)
        ·
          refine ⟨10692305383447822031748665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7128203588965214687832443 10692305383447822031748665)
          ·
            refine ⟨8019229037585866523811499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10692305383447822031748665 8019229037585866523811499)
            ·
              refine ⟨12028843556378799785717249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8019229037585866523811499 12028843556378799785717249)
              ·
                refine ⟨9021632667284099839287937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12028843556378799785717249 9021632667284099839287937)
                ·
                  refine ⟨6766224500463074879465953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9021632667284099839287937 6766224500463074879465953)
                  ·
                    refine ⟨5074668375347306159599465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6766224500463074879465953 5074668375347306159599465)
                    ·
                      refine ⟨3806001281510479619699599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5074668375347306159599465 3806001281510479619699599)
                      ·
                        rfl

theorem cell23_7412161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 2, 1, 2, 2, 2, 2].length) (baseStart_7412161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7412161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7412161 prefixEnd_7412161 := by exact prefixLift 7412161
  have htrace : WordTrace (prefixWord ++ tailWord_7412161) baseStart_7412161 baseEnd_7412161 := by
    simpa [prefixWord, tailWord_7412161, baseEnd_7412161] using wordTrace_append hprefix tailTrace_7412161
  have hstable : (prefixWord ++ tailWord_7412161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7412161).length < 2 ^ (prefixWord ++ tailWord_7412161).sum := by decide
  have hdescent : baseEnd_7412161 < baseStart_7412161 := by decide
  rcases family_descends (prefixWord ++ tailWord_7412161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7412253 : List Nat := [1, 4, 2, 2, 1, 2, 3, 2, 1, 5]
def baseStart_7412253 : Nat := 118140960795 + 7412253 * 2 ^ 59
def prefixEnd_7412253 : Nat := 4983230072969 + 3 ^ 40 * 7412253 * 2
def baseEnd_7412253 : Nat := 1268682840576897753249725

theorem tailTrace_7412253 : CollatzResearch.WordTrace tailWord_7412253 prefixEnd_7412253 1268682840576897753249725 := by
  unfold tailWord_7412253
  simp only [CollatzResearch.WordTrace]
  refine ⟨270347076815680767873105413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180231384543787178582070275 270347076815680767873105413)
  ·
    refine ⟨50690076902940143976207265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 270347076815680767873105413 50690076902940143976207265)
    ·
      refine ⟨38017557677205107982155449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50690076902940143976207265 38017557677205107982155449)
      ·
        refine ⟨28513168257903830986616587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38017557677205107982155449 28513168257903830986616587)
        ·
          refine ⟨42769752386855746479924881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28513168257903830986616587 42769752386855746479924881)
          ·
            refine ⟨32077314290141809859943661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42769752386855746479924881 32077314290141809859943661)
            ·
              refine ⟨12028992858803178697478873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32077314290141809859943661 12028992858803178697478873)
              ·
                refine ⟨9021744644102384023109155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12028992858803178697478873 9021744644102384023109155)
                ·
                  refine ⟨13532616966153576034663733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9021744644102384023109155 13532616966153576034663733)
                  ·
                    refine ⟨1268682840576897753249725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13532616966153576034663733 1268682840576897753249725)
                    ·
                      rfl

theorem cell23_7412253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 3, 2, 1, 5].length) (baseStart_7412253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7412253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7412253 prefixEnd_7412253 := by exact prefixLift 7412253
  have htrace : WordTrace (prefixWord ++ tailWord_7412253) baseStart_7412253 baseEnd_7412253 := by
    simpa [prefixWord, tailWord_7412253, baseEnd_7412253] using wordTrace_append hprefix tailTrace_7412253
  have hstable : (prefixWord ++ tailWord_7412253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7412253).length < 2 ^ (prefixWord ++ tailWord_7412253).sum := by decide
  have hdescent : baseEnd_7412253 < baseStart_7412253 := by decide
  rcases family_descends (prefixWord ++ tailWord_7412253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7412266 : List Nat := [3, 1, 4, 1, 1, 2, 1, 1, 3, 6]
def baseStart_7412266 : Nat := 118140960795 + 7412266 * 2 ^ 59
def prefixEnd_7412266 : Nat := 4983230072969 + 3 ^ 40 * 7412266 * 2
def baseEnd_7412266 : Nat := 1268685065659733902962205

theorem tailTrace_7412266 : CollatzResearch.WordTrace tailWord_7412266 prefixEnd_7412266 1268685065659733902962205 := by
  unfold tailWord_7412266
  simp only [CollatzResearch.WordTrace]
  refine ⟨67586887741158417773332163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 180231700643089114062219101 67586887741158417773332163)
  ·
    refine ⟨101380331611737626659998245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67586887741158417773332163 101380331611737626659998245)
    ·
      refine ⟨19008812177200804998749671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 101380331611737626659998245 19008812177200804998749671)
      ·
        refine ⟨28513218265801207498124507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19008812177200804998749671 28513218265801207498124507)
        ·
          refine ⟨42769827398701811247186761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28513218265801207498124507 42769827398701811247186761)
          ·
            refine ⟨32077370549026358435390071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42769827398701811247186761 32077370549026358435390071)
            ·
              refine ⟨48116055823539537653085107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32077370549026358435390071 48116055823539537653085107)
              ·
                refine ⟨72174083735309306479627661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48116055823539537653085107 72174083735309306479627661)
                ·
                  refine ⟨27065281400740989929860373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 72174083735309306479627661 27065281400740989929860373)
                  ·
                    refine ⟨1268685065659733902962205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27065281400740989929860373 1268685065659733902962205)
                    ·
                      rfl

theorem cell23_7412266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 1, 1, 3, 6].length) (baseStart_7412266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7412266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7412266 prefixEnd_7412266 := by exact prefixLift 7412266
  have htrace : WordTrace (prefixWord ++ tailWord_7412266) baseStart_7412266 baseEnd_7412266 := by
    simpa [prefixWord, tailWord_7412266, baseEnd_7412266] using wordTrace_append hprefix tailTrace_7412266
  have hstable : (prefixWord ++ tailWord_7412266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7412266).length < 2 ^ (prefixWord ++ tailWord_7412266).sum := by decide
  have hdescent : baseEnd_7412266 < baseStart_7412266 := by decide
  rcases family_descends (prefixWord ++ tailWord_7412266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7412284 : List Nat := [2, 2, 2, 2, 3, 3, 2, 2, 1, 1, 3]
def baseStart_7412284 : Nat := 118140960795 + 7412284 * 2 ^ 59
def prefixEnd_7412284 : Nat := 4983230072969 + 3 ^ 40 * 7412284 * 2
def baseEnd_7412284 : Nat := 3806064439630982638461533

theorem tailTrace_7412284 : CollatzResearch.WordTrace tailWord_7412284 prefixEnd_7412284 3806064439630982638461533 := by
  unfold tailWord_7412284
  simp only [CollatzResearch.WordTrace]
  refine ⟨135174103739284230083741953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180232138319045640111655937 135174103739284230083741953)
  ·
    refine ⟨101380577804463172562806465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135174103739284230083741953 101380577804463172562806465)
    ·
      refine ⟨76035433353347379422104849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101380577804463172562806465 76035433353347379422104849)
      ·
        refine ⟨57026575015010534566578637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76035433353347379422104849 57026575015010534566578637)
        ·
          refine ⟨21384965630628950462466989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57026575015010534566578637 21384965630628950462466989)
          ·
            refine ⟨8019362111485856423425121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21384965630628950462466989 8019362111485856423425121)
            ·
              refine ⟨6014521583614392317568841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8019362111485856423425121 6014521583614392317568841)
              ·
                refine ⟨4510891187710794238176631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6014521583614392317568841 4510891187710794238176631)
                ·
                  refine ⟨6766336781566191357264947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4510891187710794238176631 6766336781566191357264947)
                  ·
                    refine ⟨10149505172349287035897421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6766336781566191357264947 10149505172349287035897421)
                    ·
                      refine ⟨3806064439630982638461533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10149505172349287035897421 3806064439630982638461533)
                      ·
                        rfl

theorem cell23_7412284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 3, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 3, 2, 2, 1, 1, 3].length) (baseStart_7412284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7412284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7412284 prefixEnd_7412284 := by exact prefixLift 7412284
  have htrace : WordTrace (prefixWord ++ tailWord_7412284) baseStart_7412284 baseEnd_7412284 := by
    simpa [prefixWord, tailWord_7412284, baseEnd_7412284] using wordTrace_append hprefix tailTrace_7412284
  have hstable : (prefixWord ++ tailWord_7412284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7412284).length < 2 ^ (prefixWord ++ tailWord_7412284).sum := by decide
  have hdescent : baseEnd_7412284 < baseStart_7412284 := by decide
  rcases family_descends (prefixWord ++ tailWord_7412284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7412299 : List Nat := [1, 1, 1, 1, 3, 1, 4, 1, 2, 2, 6]
def baseStart_7412299 : Nat := 118140960795 + 7412299 * 2 ^ 59
def prefixEnd_7412299 : Nat := 4983230072969 + 3 ^ 40 * 7412299 * 2
def baseEnd_7412299 : Nat := 3806072141840800079773963

theorem tailTrace_7412299 : CollatzResearch.WordTrace tailWord_7412299 prefixEnd_7412299 3806072141840800079773963 := by
  unfold tailWord_7412299
  simp only [CollatzResearch.WordTrace]
  refine ⟨270348754573514117729279951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180232503049009411819519967 270348754573514117729279951)
  ·
    refine ⟨405523131860271176593919927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270348754573514117729279951 405523131860271176593919927)
    ·
      refine ⟨608284697790406764890879891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 405523131860271176593919927 608284697790406764890879891)
      ·
        refine ⟨912427046685610147336319837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 608284697790406764890879891 912427046685610147336319837)
        ·
          refine ⟨342160142507103805251119939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 912427046685610147336319837 342160142507103805251119939)
          ·
            refine ⟨513240213760655707876679909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 342160142507103805251119939 513240213760655707876679909)
            ·
              refine ⟨96232540080122945226877483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 513240213760655707876679909 96232540080122945226877483)
              ·
                refine ⟨144348810120184417840316225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 96232540080122945226877483 144348810120184417840316225)
                ·
                  refine ⟨108261607590138313380237169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 144348810120184417840316225 108261607590138313380237169)
                  ·
                    refine ⟨81196205692603735035177877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 108261607590138313380237169 81196205692603735035177877)
                    ·
                      refine ⟨3806072141840800079773963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 81196205692603735035177877 3806072141840800079773963)
                      ·
                        rfl

theorem cell23_7412299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 1, 2, 2, 6].length) (baseStart_7412299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7412299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7412299 prefixEnd_7412299 := by exact prefixLift 7412299
  have htrace : WordTrace (prefixWord ++ tailWord_7412299) baseStart_7412299 baseEnd_7412299 := by
    simpa [prefixWord, tailWord_7412299, baseEnd_7412299] using wordTrace_append hprefix tailTrace_7412299
  have hstable : (prefixWord ++ tailWord_7412299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7412299).length < 2 ^ (prefixWord ++ tailWord_7412299).sum := by decide
  have hdescent : baseEnd_7412299 < baseStart_7412299 := by decide
  rcases family_descends (prefixWord ++ tailWord_7412299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7412318 : List Nat := [4, 4, 1, 2, 1, 1, 2, 3, 1, 1, 3]
def baseStart_7412318 : Nat := 118140960795 + 7412318 * 2 ^ 59
def prefixEnd_7412318 : Nat := 4983230072969 + 3 ^ 40 * 7412318 * 2
def baseEnd_7412318 : Nat := 3806081897973235505436377

theorem tailTrace_7412318 : CollatzResearch.WordTrace tailWord_7412318 prefixEnd_7412318 3806081897973235505436377 := by
  unfold tailWord_7412318
  simp only [CollatzResearch.WordTrace]
  refine ⟨33793680945055660496777701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 180232965040296855982814405 33793680945055660496777701)
  ·
    refine ⟨6336315177197936343145819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33793680945055660496777701 6336315177197936343145819)
    ·
      refine ⟨9504472765796904514718729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6336315177197936343145819 9504472765796904514718729)
      ·
        refine ⟨7128354574347678386039047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9504472765796904514718729 7128354574347678386039047)
        ·
          refine ⟨10692531861521517579058571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7128354574347678386039047 10692531861521517579058571)
          ·
            refine ⟨16038797792282276368587857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10692531861521517579058571 16038797792282276368587857)
            ·
              refine ⟨12029098344211707276440893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16038797792282276368587857 12029098344211707276440893)
              ·
                refine ⟨4510911879079390228665335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12029098344211707276440893 4510911879079390228665335)
                ·
                  refine ⟨6766367818619085342998003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4510911879079390228665335 6766367818619085342998003)
                  ·
                    refine ⟨10149551727928628014497005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6766367818619085342998003 10149551727928628014497005)
                    ·
                      refine ⟨3806081897973235505436377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10149551727928628014497005 3806081897973235505436377)
                      ·
                        rfl

theorem cell23_7412318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 2, 3, 1, 1, 3].length) (baseStart_7412318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7412318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7412318 prefixEnd_7412318 := by exact prefixLift 7412318
  have htrace : WordTrace (prefixWord ++ tailWord_7412318) baseStart_7412318 baseEnd_7412318 := by
    simpa [prefixWord, tailWord_7412318, baseEnd_7412318] using wordTrace_append hprefix tailTrace_7412318
  have hstable : (prefixWord ++ tailWord_7412318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7412318).length < 2 ^ (prefixWord ++ tailWord_7412318).sum := by decide
  have hdescent : baseEnd_7412318 < baseStart_7412318 := by decide
  rcases family_descends (prefixWord ++ tailWord_7412318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7412323 : List Nat := [1, 1, 1, 5, 1, 2, 2, 2, 4, 1, 3]
def baseStart_7412323 : Nat := 118140960795 + 7412323 * 2 ^ 59
def prefixEnd_7412323 : Nat := 4983230072969 + 3 ^ 40 * 7412323 * 2
def baseEnd_7412323 : Nat := 3806084465376507985873853

theorem tailTrace_7412323 : CollatzResearch.WordTrace tailWord_7412323 prefixEnd_7412323 3806084465376507985873853 := by
  unfold tailWord_7412323
  simp only [CollatzResearch.WordTrace]
  refine ⟨270349629925427169828153623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180233086616951446552102415 270349629925427169828153623)
  ·
    refine ⟨405524444888140754742230435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270349629925427169828153623 405524444888140754742230435)
    ·
      refine ⟨608286667332211132113345653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 405524444888140754742230435 608286667332211132113345653)
      ·
        refine ⟨57026875062394793635626155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 608286667332211132113345653 57026875062394793635626155)
        ·
          refine ⟨85540312593592190453439233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57026875062394793635626155 85540312593592190453439233)
          ·
            refine ⟨64155234445194142840079425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85540312593592190453439233 64155234445194142840079425)
            ·
              refine ⟨48116425833895607130059569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64155234445194142840079425 48116425833895607130059569)
              ·
                refine ⟨36087319375421705347544677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48116425833895607130059569 36087319375421705347544677)
                ·
                  refine ⟨6766372382891569752664627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36087319375421705347544677 6766372382891569752664627)
                  ·
                    refine ⟨10149558574337354628996941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6766372382891569752664627 10149558574337354628996941)
                    ·
                      refine ⟨3806084465376507985873853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10149558574337354628996941 3806084465376507985873853)
                      ·
                        rfl

theorem cell23_7412323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 2, 2, 4, 1, 3].length) (baseStart_7412323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7412323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7412323 prefixEnd_7412323 := by exact prefixLift 7412323
  have htrace : WordTrace (prefixWord ++ tailWord_7412323) baseStart_7412323 baseEnd_7412323 := by
    simpa [prefixWord, tailWord_7412323, baseEnd_7412323] using wordTrace_append hprefix tailTrace_7412323
  have hstable : (prefixWord ++ tailWord_7412323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7412323).length < 2 ^ (prefixWord ++ tailWord_7412323).sum := by decide
  have hdescent : baseEnd_7412323 < baseStart_7412323 := by decide
  rcases family_descends (prefixWord ++ tailWord_7412323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7412357 : List Nat := [1, 3, 1, 1, 4, 3, 3, 1, 2, 1, 3]
def baseStart_7412357 : Nat := 118140960795 + 7412357 * 2 ^ 59
def prefixEnd_7412357 : Nat := 4983230072969 + 3 ^ 40 * 7412357 * 2
def baseEnd_7412357 : Nat := 3806101923718760852848697

theorem tailTrace_7412357 : CollatzResearch.WordTrace tailWord_7412357 prefixEnd_7412357 3806101923718760852848697 := by
  unfold tailWord_7412357
  simp only [CollatzResearch.WordTrace]
  refine ⟨270350870007303993634891325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180233913338202662423260883 270350870007303993634891325)
  ·
    refine ⟨101381576252738997613084247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 270350870007303993634891325 101381576252738997613084247)
    ·
      refine ⟨152072364379108496419626371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101381576252738997613084247 152072364379108496419626371)
      ·
        refine ⟨228108546568662744629439557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152072364379108496419626371 228108546568662744629439557)
        ·
          refine ⟨42770352481624264618019917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 228108546568662744629439557 42770352481624264618019917)
          ·
            refine ⟨16038882180609099231757469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42770352481624264618019917 16038882180609099231757469)
            ·
              refine ⟨6014580817728412211909051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16038882180609099231757469 6014580817728412211909051)
              ·
                refine ⟨9021871226592618317863577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6014580817728412211909051 9021871226592618317863577)
                ·
                  refine ⟨6766403419944463738397683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9021871226592618317863577 6766403419944463738397683)
                  ·
                    refine ⟨10149605129916695607596525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6766403419944463738397683 10149605129916695607596525)
                    ·
                      refine ⟨3806101923718760852848697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10149605129916695607596525 3806101923718760852848697)
                      ·
                        rfl

theorem cell23_7412357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 3, 1, 2, 1, 3].length) (baseStart_7412357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7412357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7412357 prefixEnd_7412357 := by exact prefixLift 7412357
  have htrace : WordTrace (prefixWord ++ tailWord_7412357) baseStart_7412357 baseEnd_7412357 := by
    simpa [prefixWord, tailWord_7412357, baseEnd_7412357] using wordTrace_append hprefix tailTrace_7412357
  have hstable : (prefixWord ++ tailWord_7412357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7412357).length < 2 ^ (prefixWord ++ tailWord_7412357).sum := by decide
  have hdescent : baseEnd_7412357 < baseStart_7412357 := by decide
  rcases family_descends (prefixWord ++ tailWord_7412357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7412363 : List Nat := [1, 1, 1, 1, 4, 1, 2, 5, 1, 4, 2]
def baseStart_7412363 : Nat := 118140960795 + 7412363 * 2 ^ 59
def prefixEnd_7412363 : Nat := 4983230072969 + 3 ^ 40 * 7412363 * 2
def baseEnd_7412363 : Nat := 3806105004602687829373669

theorem tailTrace_7412363 : CollatzResearch.WordTrace tailWord_7412363 prefixEnd_7412363 3806105004602687829373669 := by
  unfold tailWord_7412363
  simp only [CollatzResearch.WordTrace]
  refine ⟨270351088845282256659609743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180234059230188171106406495 270351088845282256659609743)
  ·
    refine ⟨405526633267923384989414615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270351088845282256659609743 405526633267923384989414615)
    ·
      refine ⟨608289949901885077484121923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 405526633267923384989414615 608289949901885077484121923)
      ·
        refine ⟨912434924852827616226182885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 608289949901885077484121923 912434924852827616226182885)
        ·
          refine ⟨171081548409905178042409291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 912434924852827616226182885 171081548409905178042409291)
          ·
            refine ⟨256622322614857767063613937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 171081548409905178042409291 256622322614857767063613937)
            ·
              refine ⟨192466741961143325297710453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 256622322614857767063613937 192466741961143325297710453)
              ·
                refine ⟨18043757058857186746660355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 192466741961143325297710453 18043757058857186746660355)
                ·
                  refine ⟨27065635588285780119990533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18043757058857186746660355 27065635588285780119990533)
                  ·
                    refine ⟨5074806672803583772498225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27065635588285780119990533 5074806672803583772498225)
                    ·
                      refine ⟨3806105004602687829373669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5074806672803583772498225 3806105004602687829373669)
                      ·
                        rfl

theorem cell23_7412363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 5, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 5, 1, 4, 2].length) (baseStart_7412363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7412363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7412363 prefixEnd_7412363 := by exact prefixLift 7412363
  have htrace : WordTrace (prefixWord ++ tailWord_7412363) baseStart_7412363 baseEnd_7412363 := by
    simpa [prefixWord, tailWord_7412363, baseEnd_7412363] using wordTrace_append hprefix tailTrace_7412363
  have hstable : (prefixWord ++ tailWord_7412363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7412363).length < 2 ^ (prefixWord ++ tailWord_7412363).sum := by decide
  have hdescent : baseEnd_7412363 < baseStart_7412363 := by decide
  rcases family_descends (prefixWord ++ tailWord_7412363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7412397 : List Nat := [1, 5, 2, 1, 1, 2, 2, 1, 4, 2, 2]
def baseStart_7412397 : Nat := 118140960795 + 7412397 * 2 ^ 59
def prefixEnd_7412397 : Nat := 4983230072969 + 3 ^ 40 * 7412397 * 2
def baseEnd_7412397 : Nat := 3806122462944940696348513

theorem tailTrace_7412397 : CollatzResearch.WordTrace tailWord_7412397 prefixEnd_7412397 3806122462944940696348513 := by
  unfold tailWord_7412397
  simp only [CollatzResearch.WordTrace]
  refine ⟨270352328927159080466347445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180234885951439386977564963 270352328927159080466347445)
  ·
    refine ⟨25345530836921163793720073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 270352328927159080466347445 25345530836921163793720073)
    ·
      refine ⟨19009148127690872845290055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25345530836921163793720073 19009148127690872845290055)
      ·
        refine ⟨28513722191536309267935083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19009148127690872845290055 28513722191536309267935083)
        ·
          refine ⟨42770583287304463901902625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28513722191536309267935083 42770583287304463901902625)
          ·
            refine ⟨32077937465478347926426969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42770583287304463901902625 32077937465478347926426969)
            ·
              refine ⟨24058453099108760944820227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32077937465478347926426969 24058453099108760944820227)
              ·
                refine ⟨36087679648663141417230341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24058453099108760944820227 36087679648663141417230341)
                ·
                  refine ⟨6766439934124339015730689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36087679648663141417230341 6766439934124339015730689)
                  ·
                    refine ⟨5074829950593254261798017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6766439934124339015730689 5074829950593254261798017)
                    ·
                      refine ⟨3806122462944940696348513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5074829950593254261798017 3806122462944940696348513)
                      ·
                        rfl

theorem cell23_7412397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 2, 1, 4, 2, 2].length) (baseStart_7412397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7412397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7412397 prefixEnd_7412397 := by exact prefixLift 7412397
  have htrace : WordTrace (prefixWord ++ tailWord_7412397) baseStart_7412397 baseEnd_7412397 := by
    simpa [prefixWord, tailWord_7412397, baseEnd_7412397] using wordTrace_append hprefix tailTrace_7412397
  have hstable : (prefixWord ++ tailWord_7412397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7412397).length < 2 ^ (prefixWord ++ tailWord_7412397).sum := by decide
  have hdescent : baseEnd_7412397 < baseStart_7412397 := by decide
  rcases family_descends (prefixWord ++ tailWord_7412397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7412403 : List Nat := [1, 1, 1, 2, 3, 6, 1, 1, 7]
def baseStart_7412403 : Nat := 118140960795 + 7412403 * 2 ^ 59
def prefixEnd_7412403 : Nat := 4983230072969 + 3 ^ 40 * 7412403 * 2
def baseEnd_7412403 : Nat := 422902838203207519208165

theorem tailTrace_7412403 : CollatzResearch.WordTrace tailWord_7412403 prefixEnd_7412403 422902838203207519208165 := by
  unfold tailWord_7412403
  simp only [CollatzResearch.WordTrace]
  refine ⟨270352547765137343491065863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180235031843424895660710575 270352547765137343491065863)
  ·
    refine ⟨405528821647706015236598795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270352547765137343491065863 405528821647706015236598795)
    ·
      refine ⟨608293232471559022854898193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 405528821647706015236598795 608293232471559022854898193)
      ·
        refine ⟨456219924353669267141173645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 608293232471559022854898193 456219924353669267141173645)
        ·
          refine ⟨171082471632625975177940117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 456219924353669267141173645 171082471632625975177940117)
          ·
            refine ⟨8019490857779342586465943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 171082471632625975177940117 8019490857779342586465943)
            ·
              refine ⟨12029236286669013879698915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8019490857779342586465943 12029236286669013879698915)
              ·
                refine ⟨18043854430003520819548373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12029236286669013879698915 18043854430003520819548373)
                ·
                  refine ⟨422902838203207519208165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18043854430003520819548373 422902838203207519208165)
                  ·
                    rfl

theorem cell23_7412403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 6, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 6, 1, 1, 7].length) (baseStart_7412403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7412403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7412403 prefixEnd_7412403 := by exact prefixLift 7412403
  have htrace : WordTrace (prefixWord ++ tailWord_7412403) baseStart_7412403 baseEnd_7412403 := by
    simpa [prefixWord, tailWord_7412403, baseEnd_7412403] using wordTrace_append hprefix tailTrace_7412403
  have hstable : (prefixWord ++ tailWord_7412403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7412403).length < 2 ^ (prefixWord ++ tailWord_7412403).sum := by decide
  have hdescent : baseEnd_7412403 < baseStart_7412403 := by decide
  rcases family_descends (prefixWord ++ tailWord_7412403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7412423 : List Nat := [1, 1, 4, 1, 1, 1, 2, 1, 4, 5, 2]
def baseStart_7412423 : Nat := 118140960795 + 7412423 * 2 ^ 59
def prefixEnd_7412423 : Nat := 4983230072969 + 3 ^ 40 * 7412423 * 2
def baseEnd_7412423 : Nat := 3806135813441957594623393

theorem tailTrace_7412423 : CollatzResearch.WordTrace tailWord_7412423 prefixEnd_7412423 3806135813441957594623393 := by
  unfold tailWord_7412423
  simp only [CollatzResearch.WordTrace]
  refine ⟨270353277225064886906793923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180235518150043257937862615 270353277225064886906793923)
  ·
    refine ⟨405529915837597330360190885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270353277225064886906793923 405529915837597330360190885)
    ·
      refine ⟨76036859219549499442535791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 405529915837597330360190885 76036859219549499442535791)
      ·
        refine ⟨114055288829324249163803687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76036859219549499442535791 114055288829324249163803687)
        ·
          refine ⟨171082933243986373745705531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114055288829324249163803687 171082933243986373745705531)
          ·
            refine ⟨256624399865979560618558297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 171082933243986373745705531 256624399865979560618558297)
            ·
              refine ⟨192468299899484670463918723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 256624399865979560618558297 192468299899484670463918723)
              ·
                refine ⟨288702449849227005695878085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 192468299899484670463918723 288702449849227005695878085)
                ·
                  refine ⟨54131709346730063567977141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 288702449849227005695878085 54131709346730063567977141)
                  ·
                    refine ⟨5074847751255943459497857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 54131709346730063567977141 5074847751255943459497857)
                    ·
                      refine ⟨3806135813441957594623393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5074847751255943459497857 3806135813441957594623393)
                      ·
                        rfl

theorem cell23_7412423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 1, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 1, 4, 5, 2].length) (baseStart_7412423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7412423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7412423 prefixEnd_7412423 := by exact prefixLift 7412423
  have htrace : WordTrace (prefixWord ++ tailWord_7412423) baseStart_7412423 baseEnd_7412423 := by
    simpa [prefixWord, tailWord_7412423, baseEnd_7412423] using wordTrace_append hprefix tailTrace_7412423
  have hstable : (prefixWord ++ tailWord_7412423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7412423).length < 2 ^ (prefixWord ++ tailWord_7412423).sum := by decide
  have hdescent : baseEnd_7412423 < baseStart_7412423 := by decide
  rcases family_descends (prefixWord ++ tailWord_7412423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7412433 : List Nat := [1, 2, 2, 1, 2, 3, 4, 1, 2, 5]
def baseStart_7412433 : Nat := 118140960795 + 7412433 * 2 ^ 59
def prefixEnd_7412433 : Nat := 4983230072969 + 3 ^ 40 * 7412433 * 2
def baseEnd_7412433 : Nat := 1268713649416167518499449

theorem tailTrace_7412433 : CollatzResearch.WordTrace tailWord_7412433 prefixEnd_7412433 1268713649416167518499449 := by
  unfold tailWord_7412433
  simp only [CollatzResearch.WordTrace]
  refine ⟨270353641955028658614657953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180235761303352439076438635 270353641955028658614657953)
  ·
    refine ⟨202765231466271493960993465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 270353641955028658614657953 202765231466271493960993465)
    ·
      refine ⟨152073923599703620470745099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 202765231466271493960993465 152073923599703620470745099)
      ·
        refine ⟨228110885399555430706117649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152073923599703620470745099 228110885399555430706117649)
        ·
          refine ⟨171083164049666573029588237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 228110885399555430706117649 171083164049666573029588237)
          ·
            refine ⟨64156186518624964886095589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 171083164049666573029588237 64156186518624964886095589)
            ·
              refine ⟨12029284972242180916142923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 64156186518624964886095589 12029284972242180916142923)
              ·
                refine ⟨18043927458363271374214385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12029284972242180916142923 18043927458363271374214385)
                ·
                  refine ⟨13532945593772453530660789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18043927458363271374214385 13532945593772453530660789)
                  ·
                    refine ⟨1268713649416167518499449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13532945593772453530660789 1268713649416167518499449)
                    ·
                      rfl

theorem cell23_7412433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 4, 1, 2, 5].length) (baseStart_7412433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7412433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7412433 prefixEnd_7412433 := by exact prefixLift 7412433
  have htrace : WordTrace (prefixWord ++ tailWord_7412433) baseStart_7412433 baseEnd_7412433 := by
    simpa [prefixWord, tailWord_7412433, baseEnd_7412433] using wordTrace_append hprefix tailTrace_7412433
  have hstable : (prefixWord ++ tailWord_7412433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7412433).length < 2 ^ (prefixWord ++ tailWord_7412433).sum := by decide
  have hdescent : baseEnd_7412433 < baseStart_7412433 := by decide
  rcases family_descends (prefixWord ++ tailWord_7412433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7412473 : List Nat := [1, 2, 1, 3, 1, 1, 1, 4, 4, 2, 3]
def baseStart_7412473 : Nat := 118140960795 + 7412473 * 2 ^ 59
def prefixEnd_7412473 : Nat := 4983230072969 + 3 ^ 40 * 7412473 * 2
def baseEnd_7412473 : Nat := 3806161487474682398998163

theorem tailTrace_7412473 : CollatzResearch.WordTrace tailWord_7412473 prefixEnd_7412473 3806161487474682398998163 := by
  unfold tailWord_7412473
  simp only [CollatzResearch.WordTrace]
  refine ⟨270355100874883745446114073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180236733916589163630742715 270355100874883745446114073)
  ·
    refine ⟨202766325656162809084585555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 270355100874883745446114073 202766325656162809084585555)
    ·
      refine ⟨304149488484244213626878333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202766325656162809084585555 304149488484244213626878333)
      ·
        refine ⟨114056058181591580110079375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 304149488484244213626878333 114056058181591580110079375)
        ·
          refine ⟨171084087272387370165119063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114056058181591580110079375 171084087272387370165119063)
          ·
            refine ⟨256626130908581055247678595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 171084087272387370165119063 256626130908581055247678595)
            ·
              refine ⟨384939196362871582871517893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 256626130908581055247678595 384939196362871582871517893)
              ·
                refine ⟨72176099318038421788409605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 384939196362871582871517893 72176099318038421788409605)
                ·
                  refine ⟨13533018622132204085326801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 72176099318038421788409605 13533018622132204085326801)
                  ·
                    refine ⟨10149763966599153063995101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13533018622132204085326801 10149763966599153063995101)
                    ·
                      refine ⟨3806161487474682398998163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10149763966599153063995101 3806161487474682398998163)
                      ·
                        rfl

theorem cell23_7412473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 4, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 4, 4, 2, 3].length) (baseStart_7412473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7412473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7412473 prefixEnd_7412473 := by exact prefixLift 7412473
  have htrace : WordTrace (prefixWord ++ tailWord_7412473) baseStart_7412473 baseEnd_7412473 := by
    simpa [prefixWord, tailWord_7412473, baseEnd_7412473] using wordTrace_append hprefix tailTrace_7412473
  have hstable : (prefixWord ++ tailWord_7412473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7412473).length < 2 ^ (prefixWord ++ tailWord_7412473).sum := by decide
  have hdescent : baseEnd_7412473 < baseStart_7412473 := by decide
  rcases family_descends (prefixWord ++ tailWord_7412473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7412487 : List Nat := [1, 1, 4, 4, 1, 3, 1, 1, 2, 1, 4]
def baseStart_7412487 : Nat := 118140960795 + 7412487 * 2 ^ 59
def prefixEnd_7412487 : Nat := 4983230072969 + 3 ^ 40 * 7412487 * 2
def baseEnd_7412487 : Nat := 3806168676203845344223099

theorem tailTrace_7412487 : CollatzResearch.WordTrace tailWord_7412487 prefixEnd_7412487 3806168676203845344223099 := by
  unfold tailWord_7412487
  simp only [CollatzResearch.WordTrace]
  refine ⟨270355611496833025837123715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180237074331222017224749143 270355611496833025837123715)
  ·
    refine ⟨405533417245249538755685573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270355611496833025837123715 405533417245249538755685573)
    ·
      refine ⟨76037515733484288516691045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 405533417245249538755685573 76037515733484288516691045)
      ·
        refine ⟨14257034200028304096879571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 76037515733484288516691045 14257034200028304096879571)
        ·
          refine ⟨21385551300042456145319357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14257034200028304096879571 21385551300042456145319357)
          ·
            refine ⟨8019581737515921054494759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21385551300042456145319357 8019581737515921054494759)
            ·
              refine ⟨12029372606273881581742139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8019581737515921054494759 12029372606273881581742139)
              ·
                refine ⟨18044058909410822372613209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12029372606273881581742139 18044058909410822372613209)
                ·
                  refine ⟨13533044182058116779459907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18044058909410822372613209 13533044182058116779459907)
                  ·
                    refine ⟨20299566273087175169189861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13533044182058116779459907 20299566273087175169189861)
                    ·
                      refine ⟨3806168676203845344223099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20299566273087175169189861 3806168676203845344223099)
                      ·
                        rfl

theorem cell23_7412487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 3, 1, 1, 2, 1, 4].length) (baseStart_7412487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7412487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7412487 prefixEnd_7412487 := by exact prefixLift 7412487
  have htrace : WordTrace (prefixWord ++ tailWord_7412487) baseStart_7412487 baseEnd_7412487 := by
    simpa [prefixWord, tailWord_7412487, baseEnd_7412487] using wordTrace_append hprefix tailTrace_7412487
  have hstable : (prefixWord ++ tailWord_7412487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7412487).length < 2 ^ (prefixWord ++ tailWord_7412487).sum := by decide
  have hdescent : baseEnd_7412487 < baseStart_7412487 := by decide
  rcases family_descends (prefixWord ++ tailWord_7412487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7412530 : List Nat := [3, 2, 1, 1, 3, 1, 1, 1, 3, 5, 2]
def baseStart_7412530 : Nat := 118140960795 + 7412530 * 2 ^ 59
def prefixEnd_7412530 : Nat := 4983230072969 + 3 ^ 40 * 7412530 * 2
def baseEnd_7412530 : Nat := 3806190755871988675985401

theorem tailTrace_7412530 : CollatzResearch.WordTrace tailWord_7412530 prefixEnd_7412530 3806190755871988675985401 := by
  unfold tailWord_7412530
  simp only [CollatzResearch.WordTrace]
  refine ⟨67589294958919311045234761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 180238119890451496120626029 67589294958919311045234761)
  ·
    refine ⟨50691971219189483283926071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67589294958919311045234761 50691971219189483283926071)
    ·
      refine ⟨76037956828784224925889107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50691971219189483283926071 76037956828784224925889107)
      ·
        refine ⟨114056935243176337388833661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76037956828784224925889107 114056935243176337388833661)
        ·
          refine ⟨42771350716191126520812623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 114056935243176337388833661 42771350716191126520812623)
          ·
            refine ⟨64157026074286689781218935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42771350716191126520812623 64157026074286689781218935)
            ·
              refine ⟨96235539111430034671828403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64157026074286689781218935 96235539111430034671828403)
              ·
                refine ⟨144353308667145052007742605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 96235539111430034671828403 144353308667145052007742605)
                ·
                  refine ⟨54132490750179394502903477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 144353308667145052007742605 54132490750179394502903477)
                  ·
                    refine ⟨5074921007829318234647201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 54132490750179394502903477 5074921007829318234647201)
                    ·
                      refine ⟨3806190755871988675985401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5074921007829318234647201 3806190755871988675985401)
                      ·
                        rfl

theorem cell23_7412530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 1, 3, 5, 2].length) (baseStart_7412530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7412530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7412530 prefixEnd_7412530 := by exact prefixLift 7412530
  have htrace : WordTrace (prefixWord ++ tailWord_7412530) baseStart_7412530 baseEnd_7412530 := by
    simpa [prefixWord, tailWord_7412530, baseEnd_7412530] using wordTrace_append hprefix tailTrace_7412530
  have hstable : (prefixWord ++ tailWord_7412530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7412530).length < 2 ^ (prefixWord ++ tailWord_7412530).sum := by decide
  have hdescent : baseEnd_7412530 < baseStart_7412530 := by decide
  rcases family_descends (prefixWord ++ tailWord_7412530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7412548 : List Nat := [2, 3, 4, 2, 1, 2, 1, 3, 1, 4]
def baseStart_7412548 : Nat := 118140960795 + 7412548 * 2 ^ 59
def prefixEnd_7412548 : Nat := 4983230072969 + 3 ^ 40 * 7412548 * 2
def baseEnd_7412548 : Nat := 1268733332841256535186773

theorem tailTrace_7412548 : CollatzResearch.WordTrace tailWord_7412548 prefixEnd_7412548 1268733332841256535186773 := by
  unfold tailWord_7412548
  simp only [CollatzResearch.WordTrace]
  refine ⟨135178918174806016627547149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180238557566408022170062865 135178918174806016627547149)
  ·
    refine ⟨50692094315552256235330181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 135178918174806016627547149 50692094315552256235330181)
    ·
      refine ⟨9504767684166048044124409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 50692094315552256235330181 9504767684166048044124409)
      ·
        refine ⟨7128575763124536033093307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9504767684166048044124409 7128575763124536033093307)
        ·
          refine ⟨10692863644686804049639961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7128575763124536033093307 10692863644686804049639961)
          ·
            refine ⟨8019647733515103037229971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10692863644686804049639961 8019647733515103037229971)
            ·
              refine ⟨12029471600272654555844957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8019647733515103037229971 12029471600272654555844957)
              ·
                refine ⟨4511051850102245458441859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12029471600272654555844957 4511051850102245458441859)
                ·
                  refine ⟨6766577775153368187662789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4511051850102245458441859 6766577775153368187662789)
                  ·
                    refine ⟨1268733332841256535186773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6766577775153368187662789 1268733332841256535186773)
                    ·
                      rfl

theorem cell23_7412548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 2, 1, 3, 1, 4].length) (baseStart_7412548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7412548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7412548 prefixEnd_7412548 := by exact prefixLift 7412548
  have htrace : WordTrace (prefixWord ++ tailWord_7412548) baseStart_7412548 baseEnd_7412548 := by
    simpa [prefixWord, tailWord_7412548, baseEnd_7412548] using wordTrace_append hprefix tailTrace_7412548
  have hstable : (prefixWord ++ tailWord_7412548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7412548).length < 2 ^ (prefixWord ++ tailWord_7412548).sum := by decide
  have hdescent : baseEnd_7412548 < baseStart_7412548 := by decide
  rcases family_descends (prefixWord ++ tailWord_7412548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7412560 : List Nat := [2, 1, 1, 1, 1, 4, 4, 3, 1, 1, 4]
def baseStart_7412560 : Nat := 118140960795 + 7412560 * 2 ^ 59
def prefixEnd_7412560 : Nat := 4983230072969 + 3 ^ 40 * 7412560 * 2
def baseEnd_7412560 : Nat := 3806206160291623558610263

theorem tailTrace_7412560 : CollatzResearch.WordTrace tailWord_7412560 prefixEnd_7412560 3806206160291623558610263 := by
  unfold tailWord_7412560
  simp only [CollatzResearch.WordTrace]
  refine ⟨135179137012784279652265567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180238849350379039536354089 135179137012784279652265567)
  ·
    refine ⟨202768705519176419478398351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135179137012784279652265567 202768705519176419478398351)
    ·
      refine ⟨304153058278764629217597527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202768705519176419478398351 304153058278764629217597527)
      ·
        refine ⟨456229587418146943826396291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 304153058278764629217597527 456229587418146943826396291)
        ·
          refine ⟨684344381127220415739594437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 456229587418146943826396291 684344381127220415739594437)
          ·
            refine ⟨128314571461353827951173957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 684344381127220415739594437 128314571461353827951173957)
            ·
              refine ⟨24058982149003842740845117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 128314571461353827951173957 24058982149003842740845117)
              ·
                refine ⟨9022118305876441027816919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24058982149003842740845117 9022118305876441027816919)
                ·
                  refine ⟨13533177458814661541725379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9022118305876441027816919 13533177458814661541725379)
                  ·
                    refine ⟨20299766188221992312588069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13533177458814661541725379 20299766188221992312588069)
                    ·
                      refine ⟨3806206160291623558610263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20299766188221992312588069 3806206160291623558610263)
                      ·
                        rfl

theorem cell23_7412560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 4, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 4, 3, 1, 1, 4].length) (baseStart_7412560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7412560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7412560 prefixEnd_7412560 := by exact prefixLift 7412560
  have htrace : WordTrace (prefixWord ++ tailWord_7412560) baseStart_7412560 baseEnd_7412560 := by
    simpa [prefixWord, tailWord_7412560, baseEnd_7412560] using wordTrace_append hprefix tailTrace_7412560
  have hstable : (prefixWord ++ tailWord_7412560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7412560).length < 2 ^ (prefixWord ++ tailWord_7412560).sum := by decide
  have hdescent : baseEnd_7412560 < baseStart_7412560 := by decide
  rcases family_descends (prefixWord ++ tailWord_7412560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7412564 : List Nat := [2, 4, 1, 1, 4, 1, 1, 2, 2, 3, 2]
def baseStart_7412564 : Nat := 118140960795 + 7412564 * 2 ^ 59
def prefixEnd_7412564 : Nat := 4983230072969 + 3 ^ 40 * 7412564 * 2
def baseEnd_7412564 : Nat := 3806208214214241542960245

theorem tailTrace_7412564 : CollatzResearch.WordTrace tailWord_7412564 prefixEnd_7412564 3806208214214241542960245 := by
  unfold tailWord_7412564
  simp only [CollatzResearch.WordTrace]
  refine ⟨135179209958777033993838373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180238946611702711991784497 135179209958777033993838373)
  ·
    refine ⟨25346101867270693873844695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 135179209958777033993838373 25346101867270693873844695)
    ·
      refine ⟨38019152800906040810767043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25346101867270693873844695 38019152800906040810767043)
      ·
        refine ⟨57028729201359061216150565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38019152800906040810767043 57028729201359061216150565)
        ·
          refine ⟨10692886725254823978028231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 57028729201359061216150565 10692886725254823978028231)
          ·
            refine ⟨16039330087882235967042347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10692886725254823978028231 16039330087882235967042347)
            ·
              refine ⟨24058995131823353950563521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16039330087882235967042347 24058995131823353950563521)
              ·
                refine ⟨18044246348867515462922641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24058995131823353950563521 18044246348867515462922641)
                ·
                  refine ⟨13533184761650636597191981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18044246348867515462922641 13533184761650636597191981)
                  ·
                    refine ⟨5074944285618988723946993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13533184761650636597191981 5074944285618988723946993)
                    ·
                      refine ⟨3806208214214241542960245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5074944285618988723946993 3806208214214241542960245)
                      ·
                        rfl

theorem cell23_7412564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 1, 2, 2, 3, 2].length) (baseStart_7412564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7412564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7412564 prefixEnd_7412564 := by exact prefixLift 7412564
  have htrace : WordTrace (prefixWord ++ tailWord_7412564) baseStart_7412564 baseEnd_7412564 := by
    simpa [prefixWord, tailWord_7412564, baseEnd_7412564] using wordTrace_append hprefix tailTrace_7412564
  have hstable : (prefixWord ++ tailWord_7412564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7412564).length < 2 ^ (prefixWord ++ tailWord_7412564).sum := by decide
  have hdescent : baseEnd_7412564 < baseStart_7412564 := by decide
  rcases family_descends (prefixWord ++ tailWord_7412564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7412570 : List Nat := [3, 1, 1, 2, 1, 4, 2, 1, 4, 4]
def baseStart_7412570 : Nat := 118140960795 + 7412570 * 2 ^ 59
def prefixEnd_7412570 : Nat := 4983230072969 + 3 ^ 40 * 7412570 * 2
def baseEnd_7412570 : Nat := 1268737098366056173161739

theorem tailTrace_7412570 : CollatzResearch.WordTrace tailWord_7412570 prefixEnd_7412570 1268737098366056173161739 := by
  unfold tailWord_7412570
  simp only [CollatzResearch.WordTrace]
  refine ⟨67589659688883082753098791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 180239092503688220674930109 67589659688883082753098791)
  ·
    refine ⟨101384489533324624129648187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67589659688883082753098791 101384489533324624129648187)
    ·
      refine ⟨152076734299986936194472281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101384489533324624129648187 152076734299986936194472281)
      ·
        refine ⟨114057550724990202145854211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 152076734299986936194472281 114057550724990202145854211)
        ·
          refine ⟨171086326087485303218781317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114057550724990202145854211 171086326087485303218781317)
          ·
            refine ⟨32078686141403494353521497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 171086326087485303218781317 32078686141403494353521497)
            ·
              refine ⟨24059014606052620765141123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32078686141403494353521497 24059014606052620765141123)
              ·
                refine ⟨36088521909078931147711685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24059014606052620765141123 36088521909078931147711685)
                ·
                  refine ⟨6766597857952299590195941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36088521909078931147711685 6766597857952299590195941)
                  ·
                    refine ⟨1268737098366056173161739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6766597857952299590195941 1268737098366056173161739)
                    ·
                      rfl

theorem cell23_7412570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 2, 1, 4, 4].length) (baseStart_7412570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7412570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7412570 prefixEnd_7412570 := by exact prefixLift 7412570
  have htrace : WordTrace (prefixWord ++ tailWord_7412570) baseStart_7412570 baseEnd_7412570 := by
    simpa [prefixWord, tailWord_7412570, baseEnd_7412570] using wordTrace_append hprefix tailTrace_7412570
  have hstable : (prefixWord ++ tailWord_7412570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7412570).length < 2 ^ (prefixWord ++ tailWord_7412570).sum := by decide
  have hdescent : baseEnd_7412570 < baseStart_7412570 := by decide
  rcases family_descends (prefixWord ++ tailWord_7412570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7412577 : List Nat := [1, 2, 3, 1, 1, 1, 2, 5, 3, 2, 2]
def baseStart_7412577 : Nat := 118140960795 + 7412577 * 2 ^ 59
def prefixEnd_7412577 : Nat := 4983230072969 + 3 ^ 40 * 7412577 * 2
def baseEnd_7412577 : Nat := 3806214889462749992097685

theorem tailTrace_7412577 : CollatzResearch.WordTrace tailWord_7412577 prefixEnd_7412577 3806214889462749992097685 := by
  unfold tailWord_7412577
  simp only [CollatzResearch.WordTrace]
  refine ⟨270358894066506971207899985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180239262711004647471933323 270358894066506971207899985)
  ·
    refine ⟨202769170549880228405924989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 270358894066506971207899985 202769170549880228405924989)
    ·
      refine ⟨76038438956205085652221871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 202769170549880228405924989 76038438956205085652221871)
      ·
        refine ⟨114057658434307628478332807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76038438956205085652221871 114057658434307628478332807)
        ·
          refine ⟨171086487651461442717499211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114057658434307628478332807 171086487651461442717499211)
          ·
            refine ⟨256629731477192164076248817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 171086487651461442717499211 256629731477192164076248817)
            ·
              refine ⟨192472298607894123057186613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 256629731477192164076248817 192472298607894123057186613)
              ·
                refine ⟨18044277994490074036611245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 192472298607894123057186613 18044277994490074036611245)
                ·
                  refine ⟨6766604247933777763729217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18044277994490074036611245 6766604247933777763729217)
                  ·
                    refine ⟨5074953185950333322796913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6766604247933777763729217 5074953185950333322796913)
                    ·
                      refine ⟨3806214889462749992097685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5074953185950333322796913 3806214889462749992097685)
                      ·
                        rfl

theorem cell23_7412577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 5, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 5, 3, 2, 2].length) (baseStart_7412577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7412577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7412577 prefixEnd_7412577 := by exact prefixLift 7412577
  have htrace : WordTrace (prefixWord ++ tailWord_7412577) baseStart_7412577 baseEnd_7412577 := by
    simpa [prefixWord, tailWord_7412577, baseEnd_7412577] using wordTrace_append hprefix tailTrace_7412577
  have hstable : (prefixWord ++ tailWord_7412577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7412577).length < 2 ^ (prefixWord ++ tailWord_7412577).sum := by decide
  have hdescent : baseEnd_7412577 < baseStart_7412577 := by decide
  rcases family_descends (prefixWord ++ tailWord_7412577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7412580 : List Nat := [2, 3, 1, 1, 4, 1, 2, 2, 1, 1, 5]
def baseStart_7412580 : Nat := 118140960795 + 7412580 * 2 ^ 59
def prefixEnd_7412580 : Nat := 4983230072969 + 3 ^ 40 * 7412580 * 2
def baseEnd_7412580 : Nat := 3806216429904713480360171

theorem tailTrace_7412580 : CollatzResearch.WordTrace tailWord_7412580 prefixEnd_7412580 3806216429904713480360171 := by
  unfold tailWord_7412580
  simp only [CollatzResearch.WordTrace]
  refine ⟨135179501742748051360129597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180239335656997401813506129 135179501742748051360129597)
  ·
    refine ⟨50692313153530519260048599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 135179501742748051360129597 50692313153530519260048599)
    ·
      refine ⟨76038469730295778890072899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50692313153530519260048599 76038469730295778890072899)
      ·
        refine ⟨114057704595443668335109349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76038469730295778890072899 114057704595443668335109349)
        ·
          refine ⟨21385819611645687812833003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 114057704595443668335109349 21385819611645687812833003)
          ·
            refine ⟨32078729417468531719249505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21385819611645687812833003 32078729417468531719249505)
            ·
              refine ⟨24059047063101398789437129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32078729417468531719249505 24059047063101398789437129)
              ·
                refine ⟨18044285297326049092077847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24059047063101398789437129 18044285297326049092077847)
                ·
                  refine ⟨27066427945989073638116771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18044285297326049092077847 27066427945989073638116771)
                  ·
                    refine ⟨40599641918983610457175157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27066427945989073638116771 40599641918983610457175157)
                    ·
                      refine ⟨3806216429904713480360171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40599641918983610457175157 3806216429904713480360171)
                      ·
                        rfl

theorem cell23_7412580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 2, 2, 1, 1, 5].length) (baseStart_7412580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7412580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7412580 prefixEnd_7412580 := by exact prefixLift 7412580
  have htrace : WordTrace (prefixWord ++ tailWord_7412580) baseStart_7412580 baseEnd_7412580 := by
    simpa [prefixWord, tailWord_7412580, baseEnd_7412580] using wordTrace_append hprefix tailTrace_7412580
  have hstable : (prefixWord ++ tailWord_7412580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7412580).length < 2 ^ (prefixWord ++ tailWord_7412580).sum := by decide
  have hdescent : baseEnd_7412580 < baseStart_7412580 := by decide
  rcases family_descends (prefixWord ++ tailWord_7412580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7412583 : List Nat := [1, 1, 5, 1, 2, 2, 1, 10]
def baseStart_7412583 : Nat := 118140960795 + 7412583 * 2 ^ 59
def prefixEnd_7412583 : Nat := 4983230072969 + 3 ^ 40 * 7412583 * 2
def baseEnd_7412583 : Nat := 140971035938765813652691

theorem tailTrace_7412583 : CollatzResearch.WordTrace tailWord_7412583 prefixEnd_7412583 140971035938765813652691 := by
  unfold tailWord_7412583
  simp only [CollatzResearch.WordTrace]
  refine ⟨270359112904485234232618403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180239408602990156155078935 270359112904485234232618403)
  ·
    refine ⟨405538669356727851348927605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270359112904485234232618403 405538669356727851348927605)
    ·
      refine ⟨38019250252193236063961963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 405538669356727851348927605 38019250252193236063961963)
      ·
        refine ⟨57028875378289854095942945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38019250252193236063961963 57028875378289854095942945)
        ·
          refine ⟨42771656533717390571957209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57028875378289854095942945 42771656533717390571957209)
          ·
            refine ⟨32078742400288042928967907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42771656533717390571957209 32078742400288042928967907)
            ·
              refine ⟨48118113600432064393451861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32078742400288042928967907 48118113600432064393451861)
              ·
                refine ⟨140971035938765813652691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 48118113600432064393451861 140971035938765813652691)
                ·
                  rfl

theorem cell23_7412583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 1, 10].length) (baseStart_7412583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7412583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7412583 prefixEnd_7412583 := by exact prefixLift 7412583
  have htrace : WordTrace (prefixWord ++ tailWord_7412583) baseStart_7412583 baseEnd_7412583 := by
    simpa [prefixWord, tailWord_7412583, baseEnd_7412583] using wordTrace_append hprefix tailTrace_7412583
  have hstable : (prefixWord ++ tailWord_7412583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7412583).length < 2 ^ (prefixWord ++ tailWord_7412583).sum := by decide
  have hdescent : baseEnd_7412583 < baseStart_7412583 := by decide
  rcases family_descends (prefixWord ++ tailWord_7412583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7412587 : List Nat := [1, 1, 1, 1, 2, 2, 8, 1, 2, 4]
def baseStart_7412587 : Nat := 118140960795 + 7412587 * 2 ^ 59
def prefixEnd_7412587 : Nat := 4983230072969 + 3 ^ 40 * 7412587 * 2
def baseEnd_7412587 : Nat := 1268740008089764984324213

theorem tailTrace_7412587 : CollatzResearch.WordTrace tailWord_7412587 prefixEnd_7412587 1268740008089764984324213 := by
  unfold tailWord_7412587
  simp only [CollatzResearch.WordTrace]
  refine ⟨270359258796470742915764015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180239505864313828610509343 270359258796470742915764015)
  ·
    refine ⟨405538888194706114373646023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270359258796470742915764015 405538888194706114373646023)
    ·
      refine ⟨608308332292059171560469035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 405538888194706114373646023 608308332292059171560469035)
      ·
        refine ⟨912462498438088757340703553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 608308332292059171560469035 912462498438088757340703553)
        ·
          refine ⟨684346873828566568005527665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 912462498438088757340703553 684346873828566568005527665)
          ·
            refine ⟨513260155371424926004145749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 684346873828566568005527665 513260155371424926004145749)
            ·
              refine ⟨6014767445758885851611083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 513260155371424926004145749 6014767445758885851611083)
              ·
                refine ⟨9022151168638328777416625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6014767445758885851611083 9022151168638328777416625)
                ·
                  refine ⟨6766613376478746583062469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9022151168638328777416625 6766613376478746583062469)
                  ·
                    refine ⟨1268740008089764984324213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6766613376478746583062469 1268740008089764984324213)
                    ·
                      rfl

theorem cell23_7412587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 8, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 8, 1, 2, 4].length) (baseStart_7412587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7412587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7412587 prefixEnd_7412587 := by exact prefixLift 7412587
  have htrace : WordTrace (prefixWord ++ tailWord_7412587) baseStart_7412587 baseEnd_7412587 := by
    simpa [prefixWord, tailWord_7412587, baseEnd_7412587] using wordTrace_append hprefix tailTrace_7412587
  have hstable : (prefixWord ++ tailWord_7412587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7412587).length < 2 ^ (prefixWord ++ tailWord_7412587).sum := by decide
  have hdescent : baseEnd_7412587 < baseStart_7412587 := by decide
  rcases family_descends (prefixWord ++ tailWord_7412587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7412597 : List Nat := [1, 3, 4, 1, 1, 3, 1, 1, 3, 2, 3]
def baseStart_7412597 : Nat := 118140960795 + 7412597 * 2 ^ 59
def prefixEnd_7412597 : Nat := 4983230072969 + 3 ^ 40 * 7412597 * 2
def baseEnd_7412597 : Nat := 3806225159075839913847593

theorem tailTrace_7412597 : CollatzResearch.WordTrace tailWord_7412597 prefixEnd_7412597 3806225159075839913847593 := by
  unfold tailWord_7412597
  simp only [CollatzResearch.WordTrace]
  refine ⟨270359623526434514623628045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180239749017623009749085363 270359623526434514623628045)
  ·
    refine ⟨101384858822412942983860517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 270359623526434514623628045 101384858822412942983860517)
    ·
      refine ⟨19009661029202426809473847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 101384858822412942983860517 19009661029202426809473847)
      ·
        refine ⟨28514491543803640214210771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19009661029202426809473847 28514491543803640214210771)
        ·
          refine ⟨42771737315705460321316157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28514491543803640214210771 42771737315705460321316157)
          ·
            refine ⟨16039401493389547620493559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42771737315705460321316157 16039401493389547620493559)
            ·
              refine ⟨24059102240084321430740339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16039401493389547620493559 24059102240084321430740339)
              ·
                refine ⟨36088653360126482146110509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24059102240084321430740339 36088653360126482146110509)
                ·
                  refine ⟨13533245010047430804791441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36088653360126482146110509 13533245010047430804791441)
                  ·
                    refine ⟨10149933757535573103593581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13533245010047430804791441 10149933757535573103593581)
                    ·
                      refine ⟨3806225159075839913847593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10149933757535573103593581 3806225159075839913847593)
                      ·
                        rfl

theorem cell23_7412597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 1, 1, 3, 2, 3].length) (baseStart_7412597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7412597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7412597 prefixEnd_7412597 := by exact prefixLift 7412597
  have htrace : WordTrace (prefixWord ++ tailWord_7412597) baseStart_7412597 baseEnd_7412597 := by
    simpa [prefixWord, tailWord_7412597, baseEnd_7412597] using wordTrace_append hprefix tailTrace_7412597
  have hstable : (prefixWord ++ tailWord_7412597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7412597).length < 2 ^ (prefixWord ++ tailWord_7412597).sum := by decide
  have hdescent : baseEnd_7412597 < baseStart_7412597 := by decide
  rcases family_descends (prefixWord ++ tailWord_7412597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7412637 : List Nat := [1, 4, 2, 1, 2, 1, 1, 1, 5, 3, 2]
def baseStart_7412637 : Nat := 118140960795 + 7412637 * 2 ^ 59
def prefixEnd_7412637 : Nat := 4983230072969 + 3 ^ 40 * 7412637 * 2
def baseEnd_7412637 : Nat := 3806245698302019757347409

theorem tailTrace_7412637 : CollatzResearch.WordTrace tailWord_7412637 prefixEnd_7412637 3806245698302019757347409 := by
  unfold tailWord_7412637
  simp only [CollatzResearch.WordTrace]
  refine ⟨270361082446289601455084165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180240721630859734303389443 270361082446289601455084165)
  ·
    refine ⟨50692702958679300272828281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 270361082446289601455084165 50692702958679300272828281)
    ·
      refine ⟨38019527219009475204621211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50692702958679300272828281 38019527219009475204621211)
      ·
        refine ⟨57029290828514212806931817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38019527219009475204621211 57029290828514212806931817)
        ·
          refine ⟨42771968121385659605198863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57029290828514212806931817 42771968121385659605198863)
          ·
            refine ⟨64157952182078489407798295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42771968121385659605198863 64157952182078489407798295)
            ·
              refine ⟨96236928273117734111697443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64157952182078489407798295 96236928273117734111697443)
              ·
                refine ⟨144355392409676601167546165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 96236928273117734111697443 144355392409676601167546165)
                ·
                  refine ⟨13533318038407181359457453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 144355392409676601167546165 13533318038407181359457453)
                  ·
                    refine ⟨5074994264402693009796545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13533318038407181359457453 5074994264402693009796545)
                    ·
                      refine ⟨3806245698302019757347409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5074994264402693009796545 3806245698302019757347409)
                      ·
                        rfl

theorem cell23_7412637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 1, 5, 3, 2].length) (baseStart_7412637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7412637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7412637 prefixEnd_7412637 := by exact prefixLift 7412637
  have htrace : WordTrace (prefixWord ++ tailWord_7412637) baseStart_7412637 baseEnd_7412637 := by
    simpa [prefixWord, tailWord_7412637, baseEnd_7412637] using wordTrace_append hprefix tailTrace_7412637
  have hstable : (prefixWord ++ tailWord_7412637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7412637).length < 2 ^ (prefixWord ++ tailWord_7412637).sum := by decide
  have hdescent : baseEnd_7412637 < baseStart_7412637 := by decide
  rcases family_descends (prefixWord ++ tailWord_7412637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7412643 : List Nat := [1, 1, 1, 4, 1, 2, 3, 1, 1, 8]
def baseStart_7412643 : Nat := 118140960795 + 7412643 * 2 ^ 59
def prefixEnd_7412643 : Nat := 4983230072969 + 3 ^ 40 * 7412643 * 2
def baseEnd_7412643 : Nat := 1268749593061982244624127

theorem tailTrace_7412643 : CollatzResearch.WordTrace tailWord_7412643 prefixEnd_7412643 1268749593061982244624127 := by
  unfold tailWord_7412643
  simp only [CollatzResearch.WordTrace]
  refine ⟨270361301284267864479802583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180240867522845242986535055 270361301284267864479802583)
  ·
    refine ⟨405541951926401796719703875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270361301284267864479802583 405541951926401796719703875)
    ·
      refine ⟨608312927889602695079555813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 405541951926401796719703875 608312927889602695079555813)
      ·
        refine ⟨114058673979300505327416715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 608312927889602695079555813 114058673979300505327416715)
        ·
          refine ⟨171088010968950757991125073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114058673979300505327416715 171088010968950757991125073)
          ·
            refine ⟨128316008226713068493343805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 171088010968950757991125073 128316008226713068493343805)
            ·
              refine ⟨48118503085017400685003927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 128316008226713068493343805 48118503085017400685003927)
              ·
                refine ⟨72177754627526101027505891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48118503085017400685003927 72177754627526101027505891)
                ·
                  refine ⟨108266631941289151541258837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 72177754627526101027505891 108266631941289151541258837)
                  ·
                    refine ⟨1268749593061982244624127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 108266631941289151541258837 1268749593061982244624127)
                    ·
                      rfl

theorem cell23_7412643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 3, 1, 1, 8].length) (baseStart_7412643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7412643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7412643 prefixEnd_7412643 := by exact prefixLift 7412643
  have htrace : WordTrace (prefixWord ++ tailWord_7412643) baseStart_7412643 baseEnd_7412643 := by
    simpa [prefixWord, tailWord_7412643, baseEnd_7412643] using wordTrace_append hprefix tailTrace_7412643
  have hstable : (prefixWord ++ tailWord_7412643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7412643).length < 2 ^ (prefixWord ++ tailWord_7412643).sum := by decide
  have hdescent : baseEnd_7412643 < baseStart_7412643 := by decide
  rcases family_descends (prefixWord ++ tailWord_7412643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7412662 : List Nat := [5, 1, 4, 1, 2, 1, 2, 1, 1, 1, 4]
def baseStart_7412662 : Nat := 118140960795 + 7412662 * 2 ^ 59
def prefixEnd_7412662 : Nat := 4983230072969 + 3 ^ 40 * 7412662 * 2
def baseEnd_7412662 : Nat := 3806258535318382159534795

theorem tailTrace_7412662 : CollatzResearch.WordTrace tailWord_7412662 prefixEnd_7412662 3806258535318382159534795 := by
  unfold tailWord_7412662
  simp only [CollatzResearch.WordTrace]
  refine ⟨16897624641949939420296515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 180241329514132687149829493 16897624641949939420296515)
  ·
    refine ⟨25346436962924909130444773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16897624641949939420296515 25346436962924909130444773)
    ·
      refine ⟨4752456930548420461958395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25346436962924909130444773 4752456930548420461958395)
      ·
        refine ⟨7128685395822630692937593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4752456930548420461958395 7128685395822630692937593)
        ·
          refine ⟨5346514046866973019703195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7128685395822630692937593 5346514046866973019703195)
          ·
            refine ⟨8019771070300459529554793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5346514046866973019703195 8019771070300459529554793)
            ·
              refine ⟨6014828302725344647166095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8019771070300459529554793 6014828302725344647166095)
              ·
                refine ⟨9022242454088016970749143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6014828302725344647166095 9022242454088016970749143)
                ·
                  refine ⟨13533363681132025456123715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9022242454088016970749143 13533363681132025456123715)
                  ·
                    refine ⟨20300045521698038184185573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13533363681132025456123715 20300045521698038184185573)
                    ·
                      refine ⟨3806258535318382159534795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20300045521698038184185573 3806258535318382159534795)
                      ·
                        rfl

theorem cell23_7412662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 2, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 2, 1, 2, 1, 1, 1, 4].length) (baseStart_7412662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7412662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7412662 prefixEnd_7412662 := by exact prefixLift 7412662
  have htrace : WordTrace (prefixWord ++ tailWord_7412662) baseStart_7412662 baseEnd_7412662 := by
    simpa [prefixWord, tailWord_7412662, baseEnd_7412662] using wordTrace_append hprefix tailTrace_7412662
  have hstable : (prefixWord ++ tailWord_7412662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7412662).length < 2 ^ (prefixWord ++ tailWord_7412662).sum := by decide
  have hdescent : baseEnd_7412662 < baseStart_7412662 := by decide
  rcases family_descends (prefixWord ++ tailWord_7412662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7412670 : List Nat := [4, 2, 1, 1, 1, 2, 2, 1, 1, 3, 5]
def baseStart_7412670 : Nat := 118140960795 + 7412670 * 2 ^ 59
def prefixEnd_7412670 : Nat := 4983230072969 + 3 ^ 40 * 7412670 * 2
def baseEnd_7412670 : Nat := 3806262643163618128234757

theorem tailTrace_7412670 : CollatzResearch.WordTrace tailWord_7412670 prefixEnd_7412670 3806262643163618128234757 := by
  unfold tailWord_7412670
  simp only [CollatzResearch.WordTrace]
  refine ⟨33795285756896256011379433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 180241524036780032060690309 33795285756896256011379433)
  ·
    refine ⟨25346464317672192008534575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33795285756896256011379433 25346464317672192008534575)
    ·
      refine ⟨38019696476508288012801863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25346464317672192008534575 38019696476508288012801863)
      ·
        refine ⟨57029544714762432019202795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38019696476508288012801863 57029544714762432019202795)
        ·
          refine ⟨85544317072143648028804193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57029544714762432019202795 85544317072143648028804193)
          ·
            refine ⟨64158237804107736021603145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85544317072143648028804193 64158237804107736021603145)
            ·
              refine ⟨48118678353080802016202359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64158237804107736021603145 48118678353080802016202359)
              ·
                refine ⟨72178017529621203024303539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48118678353080802016202359 72178017529621203024303539)
                ·
                  refine ⟨108267026294431804536455309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 72178017529621203024303539 108267026294431804536455309)
                  ·
                    refine ⟨40600134860411926701170741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 108267026294431804536455309 40600134860411926701170741)
                    ·
                      refine ⟨3806262643163618128234757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40600134860411926701170741 3806262643163618128234757)
                      ·
                        rfl

theorem cell23_7412670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 2, 1, 1, 3, 5].length) (baseStart_7412670 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7412670 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7412670 prefixEnd_7412670 := by exact prefixLift 7412670
  have htrace : WordTrace (prefixWord ++ tailWord_7412670) baseStart_7412670 baseEnd_7412670 := by
    simpa [prefixWord, tailWord_7412670, baseEnd_7412670] using wordTrace_append hprefix tailTrace_7412670
  have hstable : (prefixWord ++ tailWord_7412670).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7412670).length < 2 ^ (prefixWord ++ tailWord_7412670).sum := by decide
  have hdescent : baseEnd_7412670 < baseStart_7412670 := by decide
  rcases family_descends (prefixWord ++ tailWord_7412670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7412684 : List Nat := [2, 2, 1, 4, 1, 1, 3, 1, 4, 2, 2]
def baseStart_7412684 : Nat := 118140960795 + 7412684 * 2 ^ 59
def prefixEnd_7412684 : Nat := 4983230072969 + 3 ^ 40 * 7412684 * 2
def baseEnd_7412684 : Nat := 3806269831892781073459693

theorem tailTrace_7412684 : CollatzResearch.WordTrace tailWord_7412684 prefixEnd_7412684 3806269831892781073459693 := by
  unfold tailWord_7412684
  simp only [CollatzResearch.WordTrace]
  refine ⟨135181398338559664241022553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180241864451412885654696737 135181398338559664241022553)
  ·
    refine ⟨101386048753919748180766915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135181398338559664241022553 101386048753919748180766915)
    ·
      refine ⟨152079073130879622271150373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101386048753919748180766915 152079073130879622271150373)
      ·
        refine ⟨28514826212039929175840695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 152079073130879622271150373 28514826212039929175840695)
        ·
          refine ⟨42772239318059893763761043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28514826212039929175840695 42772239318059893763761043)
          ·
            refine ⟨64158358977089840645641565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42772239318059893763761043 64158358977089840645641565)
            ·
              refine ⟨24059384616408690242115587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64158358977089840645641565 24059384616408690242115587)
              ·
                refine ⟨36089076924613035363173381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24059384616408690242115587 36089076924613035363173381)
                ·
                  refine ⟨6766701923364944130595009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36089076924613035363173381 6766701923364944130595009)
                  ·
                    refine ⟨5075026442523708097946257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6766701923364944130595009 5075026442523708097946257)
                    ·
                      refine ⟨3806269831892781073459693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5075026442523708097946257 3806269831892781073459693)
                      ·
                        rfl

theorem cell23_7412684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 3, 1, 4, 2, 2].length) (baseStart_7412684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7412684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7412684 prefixEnd_7412684 := by exact prefixLift 7412684
  have htrace : WordTrace (prefixWord ++ tailWord_7412684) baseStart_7412684 baseEnd_7412684 := by
    simpa [prefixWord, tailWord_7412684, baseEnd_7412684] using wordTrace_append hprefix tailTrace_7412684
  have hstable : (prefixWord ++ tailWord_7412684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7412684).length < 2 ^ (prefixWord ++ tailWord_7412684).sum := by decide
  have hdescent : baseEnd_7412684 < baseStart_7412684 := by decide
  rcases family_descends (prefixWord ++ tailWord_7412684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7412701 : List Nat := [1, 4, 3, 1, 2, 3, 1, 1, 1, 4, 2]
def baseStart_7412701 : Nat := 118140960795 + 7412701 * 2 ^ 59
def prefixEnd_7412701 : Nat := 4983230072969 + 3 ^ 40 * 7412701 * 2
def baseEnd_7412701 : Nat := 3806278561063907506947115

theorem tailTrace_7412701 : CollatzResearch.WordTrace tailWord_7412701 prefixEnd_7412701 3806278561063907506947115 := by
  unfold tailWord_7412701
  simp only [CollatzResearch.WordTrace]
  refine ⟨270363416718057740385413957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180242277812038493590275971 270363416718057740385413957)
  ·
    refine ⟨50693140634635826322265117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 270363416718057740385413957 50693140634635826322265117)
    ·
      refine ⟨19009927737988434870849419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50693140634635826322265117 19009927737988434870849419)
      ·
        refine ⟨28514891606982652306274129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19009927737988434870849419 28514891606982652306274129)
        ·
          refine ⟨21386168705236989229705597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28514891606982652306274129 21386168705236989229705597)
          ·
            refine ⟨8019813264463870961139599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21386168705236989229705597 8019813264463870961139599)
            ·
              refine ⟨12029719896695806441709399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8019813264463870961139599 12029719896695806441709399)
              ·
                refine ⟨18044579845043709662564099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12029719896695806441709399 18044579845043709662564099)
                ·
                  refine ⟨27066869767565564493846149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18044579845043709662564099 27066869767565564493846149)
                  ·
                    refine ⟨5075038081418543342596153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27066869767565564493846149 5075038081418543342596153)
                    ·
                      refine ⟨3806278561063907506947115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5075038081418543342596153 3806278561063907506947115)
                      ·
                        rfl

theorem cell23_7412701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 3, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 3, 1, 1, 1, 4, 2].length) (baseStart_7412701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7412701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7412701 prefixEnd_7412701 := by exact prefixLift 7412701
  have htrace : WordTrace (prefixWord ++ tailWord_7412701) baseStart_7412701 baseEnd_7412701 := by
    simpa [prefixWord, tailWord_7412701, baseEnd_7412701] using wordTrace_append hprefix tailTrace_7412701
  have hstable : (prefixWord ++ tailWord_7412701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7412701).length < 2 ^ (prefixWord ++ tailWord_7412701).sum := by decide
  have hdescent : baseEnd_7412701 < baseStart_7412701 := by decide
  rcases family_descends (prefixWord ++ tailWord_7412701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7412720 : List Nat := [2, 1, 1, 1, 3, 2, 1, 5, 2, 5]
def baseStart_7412720 : Nat := 118140960795 + 7412720 * 2 ^ 59
def prefixEnd_7412720 : Nat := 4983230072969 + 3 ^ 40 * 7412720 * 2
def baseEnd_7412720 : Nat := 1268762772398780977536509

theorem tailTrace_7412720 : CollatzResearch.WordTrace tailWord_7412720 prefixEnd_7412720 1268762772398780977536509 := by
  unfold tailWord_7412720
  simp only [CollatzResearch.WordTrace]
  refine ⟨135182054852494453315177807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180242739803325937753570409 135182054852494453315177807)
  ·
    refine ⟨202773082278741679972766711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135182054852494453315177807 202773082278741679972766711)
    ·
      refine ⟨304159623418112519959150067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202773082278741679972766711 304159623418112519959150067)
      ·
        refine ⟨456239435127168779938725101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 304159623418112519959150067 456239435127168779938725101)
        ·
          refine ⟨171089788172688292477021913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 456239435127168779938725101 171089788172688292477021913)
          ·
            refine ⟨128317341129516219357766435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 171089788172688292477021913 128317341129516219357766435)
            ·
              refine ⟨192476011694274329036649653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 128317341129516219357766435 192476011694274329036649653)
              ·
                refine ⟨18044626096338218347185905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 192476011694274329036649653 18044626096338218347185905)
                ·
                  refine ⟨13533469572253663760389429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18044626096338218347185905 13533469572253663760389429)
                  ·
                    refine ⟨1268762772398780977536509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13533469572253663760389429 1268762772398780977536509)
                    ·
                      rfl

theorem cell23_7412720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 5, 2, 5].length) (baseStart_7412720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7412720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7412720 prefixEnd_7412720 := by exact prefixLift 7412720
  have htrace : WordTrace (prefixWord ++ tailWord_7412720) baseStart_7412720 baseEnd_7412720 := by
    simpa [prefixWord, tailWord_7412720, baseEnd_7412720] using wordTrace_append hprefix tailTrace_7412720
  have hstable : (prefixWord ++ tailWord_7412720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7412720).length < 2 ^ (prefixWord ++ tailWord_7412720).sum := by decide
  have hdescent : baseEnd_7412720 < baseStart_7412720 := by decide
  rcases family_descends (prefixWord ++ tailWord_7412720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7412737 : List Nat := [1, 2, 4, 1, 2, 3, 1, 2, 2, 5]
def baseStart_7412737 : Nat := 118140960795 + 7412737 * 2 ^ 59
def prefixEnd_7412737 : Nat := 4983230072969 + 3 ^ 40 * 7412737 * 2
def baseEnd_7412737 : Nat := 1268765682122489788698983

theorem tailTrace_7412737 : CollatzResearch.WordTrace tailWord_7412737 prefixEnd_7412737 1268765682122489788698983 := by
  unfold tailWord_7412737
  simp only [CollatzResearch.WordTrace]
  refine ⟨270364729745927318533724465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180243153163951545689149643 270364729745927318533724465)
  ·
    refine ⟨202773547309445488900293349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 270364729745927318533724465 202773547309445488900293349)
    ·
      refine ⟨38020040120521029168805003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 202773547309445488900293349 38020040120521029168805003)
      ·
        refine ⟨57030060180781543753207505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38020040120521029168805003 57030060180781543753207505)
        ·
          refine ⟨42772545135586157814905629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57030060180781543753207505 42772545135586157814905629)
          ·
            refine ⟨16039704425844809180589611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42772545135586157814905629 16039704425844809180589611)
            ·
              refine ⟨24059556638767213770884417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16039704425844809180589611 24059556638767213770884417)
              ·
                refine ⟨18044667479075410328163313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24059556638767213770884417 18044667479075410328163313)
                ·
                  refine ⟨13533500609306557746122485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18044667479075410328163313 13533500609306557746122485)
                  ·
                    refine ⟨1268765682122489788698983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13533500609306557746122485 1268765682122489788698983)
                    ·
                      rfl

theorem cell23_7412737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 1, 2, 2, 5].length) (baseStart_7412737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7412737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7412737 prefixEnd_7412737 := by exact prefixLift 7412737
  have htrace : WordTrace (prefixWord ++ tailWord_7412737) baseStart_7412737 baseEnd_7412737 := by
    simpa [prefixWord, tailWord_7412737, baseEnd_7412737] using wordTrace_append hprefix tailTrace_7412737
  have hstable : (prefixWord ++ tailWord_7412737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7412737).length < 2 ^ (prefixWord ++ tailWord_7412737).sum := by decide
  have hdescent : baseEnd_7412737 < baseStart_7412737 := by decide
  rcases family_descends (prefixWord ++ tailWord_7412737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7412784 : List Nat := [2, 1, 1, 1, 2, 4, 2, 5, 1, 4]
def baseStart_7412784 : Nat := 118140960795 + 7412784 * 2 ^ 59
def prefixEnd_7412784 : Nat := 4983230072969 + 3 ^ 40 * 7412784 * 2
def baseEnd_7412784 : Nat := 1268773726652743560736411

theorem tailTrace_7412784 : CollatzResearch.WordTrace tailWord_7412784 prefixEnd_7412784 1268773726652743560736411 := by
  unfold tailWord_7412784
  simp only [CollatzResearch.WordTrace]
  refine ⟨135183221988378522780342703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180244295984504697040456937 135183221988378522780342703)
  ·
    refine ⟨202774832982567784170514055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135183221988378522780342703 202774832982567784170514055)
    ·
      refine ⟨304162249473851676255771083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202774832982567784170514055 304162249473851676255771083)
      ·
        refine ⟨456243374210777514383656625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 304162249473851676255771083 456243374210777514383656625)
        ·
          refine ⟨342182530658083135787742469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 456243374210777514383656625 342182530658083135787742469)
          ·
            refine ⟨64159224498390587960201713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 342182530658083135787742469 64159224498390587960201713)
            ·
              refine ⟨48119418373792940970151285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64159224498390587960201713 48119418373792940970151285)
              ·
                refine ⟨4511195472543088215951683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 48119418373792940970151285 4511195472543088215951683)
                ·
                  refine ⟨6766793208814632323927525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4511195472543088215951683 6766793208814632323927525)
                  ·
                    refine ⟨1268773726652743560736411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6766793208814632323927525 1268773726652743560736411)
                    ·
                      rfl

theorem cell23_7412784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 2, 5, 1, 4].length) (baseStart_7412784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7412784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7412784 prefixEnd_7412784 := by exact prefixLift 7412784
  have htrace : WordTrace (prefixWord ++ tailWord_7412784) baseStart_7412784 baseEnd_7412784 := by
    simpa [prefixWord, tailWord_7412784, baseEnd_7412784] using wordTrace_append hprefix tailTrace_7412784
  have hstable : (prefixWord ++ tailWord_7412784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7412784).length < 2 ^ (prefixWord ++ tailWord_7412784).sum := by decide
  have hdescent : baseEnd_7412784 < baseStart_7412784 := by decide
  rcases family_descends (prefixWord ++ tailWord_7412784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7412797 : List Nat := [1, 4, 1, 3, 1, 2, 1, 4, 6]
def baseStart_7412797 : Nat := 118140960795 + 7412797 * 2 ^ 59
def prefixEnd_7412797 : Nat := 4983230072969 + 3 ^ 40 * 7412797 * 2
def baseEnd_7412797 : Nat := 422925317245193236816297

theorem tailTrace_7412797 : CollatzResearch.WordTrace tailWord_7412797 prefixEnd_7412797 422925317245193236816297 := by
  unfold tailWord_7412797
  simp only [CollatzResearch.WordTrace]
  refine ⟨270366918125709948780908645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180244612083806632520605763 270366918125709948780908645)
  ·
    refine ⟨50693797148570615396420371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 270366918125709948780908645 50693797148570615396420371)
    ·
      refine ⟨76040695722855923094630557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50693797148570615396420371 76040695722855923094630557)
      ·
        refine ⟨28515260896070971160486459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76040695722855923094630557 28515260896070971160486459)
        ·
          refine ⟨42772891344106456740729689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28515260896070971160486459 42772891344106456740729689)
          ·
            refine ⟨32079668508079842555547267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42772891344106456740729689 32079668508079842555547267)
            ·
              refine ⟨48119502762119763833320901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32079668508079842555547267 48119502762119763833320901)
              ·
                refine ⟨9022406767897455718747669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48119502762119763833320901 9022406767897455718747669)
                ·
                  refine ⟨422925317245193236816297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9022406767897455718747669 422925317245193236816297)
                  ·
                    rfl

theorem cell23_7412797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 1, 4, 6].length) (baseStart_7412797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7412797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7412797 prefixEnd_7412797 := by exact prefixLift 7412797
  have htrace : WordTrace (prefixWord ++ tailWord_7412797) baseStart_7412797 baseEnd_7412797 := by
    simpa [prefixWord, tailWord_7412797, baseEnd_7412797] using wordTrace_append hprefix tailTrace_7412797
  have hstable : (prefixWord ++ tailWord_7412797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7412797).length < 2 ^ (prefixWord ++ tailWord_7412797).sum := by decide
  have hdescent : baseEnd_7412797 < baseStart_7412797 := by decide
  rcases family_descends (prefixWord ++ tailWord_7412797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7412800 : List Nat := [2, 1, 1, 2, 2, 3, 2, 1, 1, 2, 6]
def baseStart_7412800 : Nat := 118140960795 + 7412800 * 2 ^ 59
def prefixEnd_7412800 : Nat := 4983230072969 + 3 ^ 40 * 7412800 * 2
def baseEnd_7412800 : Nat := 3806329395648702619609159

theorem tailTrace_7412800 : CollatzResearch.WordTrace tailWord_7412800 prefixEnd_7412800 3806329395648702619609159 := by
  unfold tailWord_7412800
  simp only [CollatzResearch.WordTrace]
  refine ⟨135183513772349540146633927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180244685029799386862178569 135183513772349540146633927)
  ·
    refine ⟨202775270658524310219950891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135183513772349540146633927 202775270658524310219950891)
    ·
      refine ⟨304162905987786465329926337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202775270658524310219950891 304162905987786465329926337)
      ·
        refine ⟨228122179490839848997444753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 304162905987786465329926337 228122179490839848997444753)
        ·
          refine ⟨171091634618129886748083565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 228122179490839848997444753 171091634618129886748083565)
          ·
            refine ⟨64159362981798707530531337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 171091634618129886748083565 64159362981798707530531337)
            ·
              refine ⟨48119522236349030647898503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64159362981798707530531337 48119522236349030647898503)
              ·
                refine ⟨72179283354523545971847755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48119522236349030647898503 72179283354523545971847755)
                ·
                  refine ⟨108268925031785318957771633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 72179283354523545971847755 108268925031785318957771633)
                  ·
                    refine ⟨81201693773838989218328725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 108268925031785318957771633 81201693773838989218328725)
                    ·
                      refine ⟨3806329395648702619609159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 81201693773838989218328725 3806329395648702619609159)
                      ·
                        rfl

theorem cell23_7412800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 2, 1, 1, 2, 6].length) (baseStart_7412800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7412800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7412800 prefixEnd_7412800 := by exact prefixLift 7412800
  have htrace : WordTrace (prefixWord ++ tailWord_7412800) baseStart_7412800 baseEnd_7412800 := by
    simpa [prefixWord, tailWord_7412800, baseEnd_7412800] using wordTrace_append hprefix tailTrace_7412800
  have hstable : (prefixWord ++ tailWord_7412800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7412800).length < 2 ^ (prefixWord ++ tailWord_7412800).sum := by decide
  have hdescent : baseEnd_7412800 < baseStart_7412800 := by decide
  rcases family_descends (prefixWord ++ tailWord_7412800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7412824 : List Nat := [2, 1, 2, 2, 1, 3, 3, 2, 3, 1, 3]
def baseStart_7412824 : Nat := 118140960795 + 7412824 * 2 ^ 59
def prefixEnd_7412824 : Nat := 4983230072969 + 3 ^ 40 * 7412824 * 2
def baseEnd_7412824 : Nat := 3806341719184410525709049

theorem tailTrace_7412824 : CollatzResearch.WordTrace tailWord_7412824 prefixEnd_7412824 3806341719184410525709049 := by
  unfold tailWord_7412824
  simp only [CollatzResearch.WordTrace]
  refine ⟨135183951448306066196070763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180245268597741421594761017 135183951448306066196070763)
  ·
    refine ⟨202775927172459099294106145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135183951448306066196070763 202775927172459099294106145)
    ·
      refine ⟨152081945379344324470579609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 202775927172459099294106145 152081945379344324470579609)
      ·
        refine ⟨114061459034508243352934707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 152081945379344324470579609 114061459034508243352934707)
        ·
          refine ⟨171092188551762365029402061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114061459034508243352934707 171092188551762365029402061)
          ·
            refine ⟨64159570706910886886025773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 171092188551762365029402061 64159570706910886886025773)
            ·
              refine ⟨24059839015091582582259665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64159570706910886886025773 24059839015091582582259665)
              ·
                refine ⟨18044879261318686936694749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24059839015091582582259665 18044879261318686936694749)
                ·
                  refine ⟨6766829722994507601260531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18044879261318686936694749 6766829722994507601260531)
                  ·
                    refine ⟨10150244584491761401890797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6766829722994507601260531 10150244584491761401890797)
                    ·
                      refine ⟨3806341719184410525709049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10150244584491761401890797 3806341719184410525709049)
                      ·
                        rfl

theorem cell23_7412824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 3, 2, 3, 1, 3].length) (baseStart_7412824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7412824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7412824 prefixEnd_7412824 := by exact prefixLift 7412824
  have htrace : WordTrace (prefixWord ++ tailWord_7412824) baseStart_7412824 baseEnd_7412824 := by
    simpa [prefixWord, tailWord_7412824, baseEnd_7412824] using wordTrace_append hprefix tailTrace_7412824
  have hstable : (prefixWord ++ tailWord_7412824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7412824).length < 2 ^ (prefixWord ++ tailWord_7412824).sum := by decide
  have hdescent : baseEnd_7412824 < baseStart_7412824 := by decide
  rcases family_descends (prefixWord ++ tailWord_7412824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7412841 : List Nat := [1, 2, 1, 1, 1, 6, 1, 5, 1, 1, 3]
def baseStart_7412841 : Nat := 118140960795 + 7412841 * 2 ^ 59
def prefixEnd_7412841 : Nat := 4983230072969 + 3 ^ 40 * 7412841 * 2
def baseEnd_7412841 : Nat := 3806350448355536959196471

theorem tailTrace_7412841 : CollatzResearch.WordTrace tailWord_7412841 prefixEnd_7412841 3806350448355536959196471 := by
  unfold tailWord_7412841
  simp only [CollatzResearch.WordTrace]
  refine ⟨270368522937550544295510377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180245681958367029530340251 270368522937550544295510377)
  ·
    refine ⟨202776392203162908221632783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 270368522937550544295510377 202776392203162908221632783)
    ·
      refine ⟨304164588304744362332449175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202776392203162908221632783 304164588304744362332449175)
      ·
        refine ⟨456246882457116543498673763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 304164588304744362332449175 456246882457116543498673763)
        ·
          refine ⟨684370323685674815248010645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 456246882457116543498673763 684370323685674815248010645)
          ·
            refine ⟨32079858922766006964750499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 684370323685674815248010645 32079858922766006964750499)
            ·
              refine ⟨48119788384149010447125749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32079858922766006964750499 48119788384149010447125749)
              ·
                refine ⟨4511230161013969729418039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 48119788384149010447125749 4511230161013969729418039)
                ·
                  refine ⟨6766845241520954594127059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4511230161013969729418039 6766845241520954594127059)
                  ·
                    refine ⟨10150267862281431891190589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6766845241520954594127059 10150267862281431891190589)
                    ·
                      refine ⟨3806350448355536959196471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10150267862281431891190589 3806350448355536959196471)
                      ·
                        rfl

theorem cell23_7412841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 1, 5, 1, 1, 3].length) (baseStart_7412841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7412841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7412841 prefixEnd_7412841 := by exact prefixLift 7412841
  have htrace : WordTrace (prefixWord ++ tailWord_7412841) baseStart_7412841 baseEnd_7412841 := by
    simpa [prefixWord, tailWord_7412841, baseEnd_7412841] using wordTrace_append hprefix tailTrace_7412841
  have hstable : (prefixWord ++ tailWord_7412841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7412841).length < 2 ^ (prefixWord ++ tailWord_7412841).sum := by decide
  have hdescent : baseEnd_7412841 < baseStart_7412841 := by decide
  rcases family_descends (prefixWord ++ tailWord_7412841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7412867 : List Nat := [1, 1, 1, 3, 3, 2, 3, 2, 1, 1, 5]
def baseStart_7412867 : Nat := 118140960795 + 7412867 * 2 ^ 59
def prefixEnd_7412867 : Nat := 4983230072969 + 3 ^ 40 * 7412867 * 2
def baseEnd_7412867 : Nat := 3806363798852553857471351

theorem tailTrace_7412867 : CollatzResearch.WordTrace tailWord_7412867 prefixEnd_7412867 3806363798852553857471351 := by
  unfold tailWord_7412867
  simp only [CollatzResearch.WordTrace]
  refine ⟨270369471235456350735956855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180246314156970900490637903 270369471235456350735956855)
  ·
    refine ⟨405554206853184526103935283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270369471235456350735956855 405554206853184526103935283)
    ·
      refine ⟨608331310279776789155902925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 405554206853184526103935283 608331310279776789155902925)
      ·
        refine ⟨228124241354916295933463597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 608331310279776789155902925 228124241354916295933463597)
        ·
          refine ⟨85546590508093610975048849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 228124241354916295933463597 85546590508093610975048849)
          ·
            refine ⟨64159942881070208231286637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85546590508093610975048849 64159942881070208231286637)
            ·
              refine ⟨24059978580401328086732489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64159942881070208231286637 24059978580401328086732489)
              ·
                refine ⟨18044983935300996065049367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24059978580401328086732489 18044983935300996065049367)
                ·
                  refine ⟨27067475902951494097574051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18044983935300996065049367 27067475902951494097574051)
                  ·
                    refine ⟨40601213854427241146361077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27067475902951494097574051 40601213854427241146361077)
                    ·
                      refine ⟨3806363798852553857471351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40601213854427241146361077 3806363798852553857471351)
                      ·
                        rfl

theorem cell23_7412867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 3, 2, 1, 1, 5].length) (baseStart_7412867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7412867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7412867 prefixEnd_7412867 := by exact prefixLift 7412867
  have htrace : WordTrace (prefixWord ++ tailWord_7412867) baseStart_7412867 baseEnd_7412867 := by
    simpa [prefixWord, tailWord_7412867, baseEnd_7412867] using wordTrace_append hprefix tailTrace_7412867
  have hstable : (prefixWord ++ tailWord_7412867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7412867).length < 2 ^ (prefixWord ++ tailWord_7412867).sum := by decide
  have hdescent : baseEnd_7412867 < baseStart_7412867 := by decide
  rcases family_descends (prefixWord ++ tailWord_7412867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7412887 : List Nat := [1, 1, 3, 3, 3, 2, 1, 9]
def baseStart_7412887 : Nat := 118140960795 + 7412887 * 2 ^ 59
def prefixEnd_7412887 : Nat := 4983230072969 + 3 ^ 40 * 7412887 * 2
def baseEnd_7412887 : Nat := 140976817350579399230417

theorem tailTrace_7412887 : CollatzResearch.WordTrace tailWord_7412887 prefixEnd_7412887 140976817350579399230417 := by
  unfold tailWord_7412887
  simp only [CollatzResearch.WordTrace]
  refine ⟨270370200695383894151684915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180246800463589262767789943 270370200695383894151684915)
  ·
    refine ⟨405555301043075841227527373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270370200695383894151684915 405555301043075841227527373)
    ·
      refine ⟨152083237891153440460322765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 405555301043075841227527373 152083237891153440460322765)
      ·
        refine ⟨57031214209182540172621037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 152083237891153440460322765 57031214209182540172621037)
        ·
          refine ⟨21386705328443452564732889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57031214209182540172621037 21386705328443452564732889)
          ·
            refine ⟨16040028996332589423549667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21386705328443452564732889 16040028996332589423549667)
            ·
              refine ⟨24060043494498884135324501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16040028996332589423549667 24060043494498884135324501)
              ·
                refine ⟨140976817350579399230417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 24060043494498884135324501 140976817350579399230417)
                ·
                  rfl

theorem cell23_7412887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 1, 9].length) (baseStart_7412887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7412887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7412887 prefixEnd_7412887 := by exact prefixLift 7412887
  have htrace : WordTrace (prefixWord ++ tailWord_7412887) baseStart_7412887 baseEnd_7412887 := by
    simpa [prefixWord, tailWord_7412887, baseEnd_7412887] using wordTrace_append hprefix tailTrace_7412887
  have hstable : (prefixWord ++ tailWord_7412887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7412887).length < 2 ^ (prefixWord ++ tailWord_7412887).sum := by decide
  have hdescent : baseEnd_7412887 < baseStart_7412887 := by decide
  rcases family_descends (prefixWord ++ tailWord_7412887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7412948 : List Nat := [2, 4, 1, 4, 1, 1, 1, 2, 1, 3, 3]
def baseStart_7412948 : Nat := 118140960795 + 7412948 * 2 ^ 59
def prefixEnd_7412948 : Nat := 4983230072969 + 3 ^ 40 * 7412948 * 2
def baseEnd_7412948 : Nat := 3806405390785568040558479

theorem tailTrace_7412948 : CollatzResearch.WordTrace tailWord_7412948 prefixEnd_7412948 3806405390785568040558479 := by
  unfold tailWord_7412948
  simp only [CollatzResearch.WordTrace]
  refine ⟨135186212774081450784827749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180248283698775267713103665 135186212774081450784827749)
  ·
    refine ⟨25347414895140272022155203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 135186212774081450784827749 25347414895140272022155203)
    ·
      refine ⟨38021122342710408033232805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25347414895140272022155203 38021122342710408033232805)
      ·
        refine ⟨7128960439258201506231151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38021122342710408033232805 7128960439258201506231151)
        ·
          refine ⟨10693440658887302259346727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7128960439258201506231151 10693440658887302259346727)
          ·
            refine ⟨16040160988330953389020091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10693440658887302259346727 16040160988330953389020091)
            ·
              refine ⟨24060241482496430083530137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16040160988330953389020091 24060241482496430083530137)
              ·
                refine ⟨18045181111872322562647603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24060241482496430083530137 18045181111872322562647603)
                ·
                  refine ⟨27067771667808483843971405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18045181111872322562647603 27067771667808483843971405)
                  ·
                    refine ⟨10150414375428181441489277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27067771667808483843971405 10150414375428181441489277)
                    ·
                      refine ⟨3806405390785568040558479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10150414375428181441489277 3806405390785568040558479)
                      ·
                        rfl

theorem cell23_7412948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 1, 2, 1, 3, 3].length) (baseStart_7412948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7412948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7412948 prefixEnd_7412948 := by exact prefixLift 7412948
  have htrace : WordTrace (prefixWord ++ tailWord_7412948) baseStart_7412948 baseEnd_7412948 := by
    simpa [prefixWord, tailWord_7412948, baseEnd_7412948] using wordTrace_append hprefix tailTrace_7412948
  have hstable : (prefixWord ++ tailWord_7412948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7412948).length < 2 ^ (prefixWord ++ tailWord_7412948).sum := by decide
  have hdescent : baseEnd_7412948 < baseStart_7412948 := by decide
  rcases family_descends (prefixWord ++ tailWord_7412948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7412974 : List Nat := [4, 1, 2, 1, 1, 1, 3, 1, 2, 4, 3]
def baseStart_7412974 : Nat := 118140960795 + 7412974 * 2 ^ 59
def prefixEnd_7412974 : Nat := 4983230072969 + 3 ^ 40 * 7412974 * 2
def baseEnd_7412974 : Nat := 3806418741282584938833359

theorem tailTrace_7412974 : CollatzResearch.WordTrace tailWord_7412974 prefixEnd_7412974 3806418741282584938833359 := by
  unfold tailWord_7412974
  simp only [CollatzResearch.WordTrace]
  refine ⟨33796671730758588501262747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 180248915897379138673401317 33796671730758588501262747)
  ·
    refine ⟨50695007596137882751894121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33796671730758588501262747 50695007596137882751894121)
    ·
      refine ⟨38021255697103412063920591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50695007596137882751894121 38021255697103412063920591)
      ·
        refine ⟨57031883545655118095880887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38021255697103412063920591 57031883545655118095880887)
        ·
          refine ⟨85547825318482677143821331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57031883545655118095880887 85547825318482677143821331)
          ·
            refine ⟨128321737977724015715731997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85547825318482677143821331 128321737977724015715731997)
            ·
              refine ⟨48120651741646505893399499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 128321737977724015715731997 48120651741646505893399499)
              ·
                refine ⟨72180977612469758840099249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48120651741646505893399499 72180977612469758840099249)
                ·
                  refine ⟨54135733209352319130074437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 72180977612469758840099249 54135733209352319130074437)
                  ·
                    refine ⟨10150449976753559836888957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 54135733209352319130074437 10150449976753559836888957)
                    ·
                      refine ⟨3806418741282584938833359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10150449976753559836888957 3806418741282584938833359)
                      ·
                        rfl

theorem cell23_7412974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 3, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 3, 1, 2, 4, 3].length) (baseStart_7412974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7412974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7412974 prefixEnd_7412974 := by exact prefixLift 7412974
  have htrace : WordTrace (prefixWord ++ tailWord_7412974) baseStart_7412974 baseEnd_7412974 := by
    simpa [prefixWord, tailWord_7412974, baseEnd_7412974] using wordTrace_append hprefix tailTrace_7412974
  have hstable : (prefixWord ++ tailWord_7412974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7412974).length < 2 ^ (prefixWord ++ tailWord_7412974).sum := by decide
  have hdescent : baseEnd_7412974 < baseStart_7412974 := by decide
  rcases family_descends (prefixWord ++ tailWord_7412974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7412977 : List Nat := [1, 2, 2, 2, 2, 1, 1, 5, 7]
def baseStart_7412977 : Nat := 118140960795 + 7412977 * 2 ^ 59
def prefixEnd_7412977 : Nat := 4983230072969 + 3 ^ 40 * 7412977 * 2
def baseEnd_7412977 : Nat := 422935586858283158566205

theorem tailTrace_7412977 : CollatzResearch.WordTrace tailWord_7412977 prefixEnd_7412977 422935586858283158566205 := by
  unfold tailWord_7412977
  simp only [CollatzResearch.WordTrace]
  refine ⟨270373483265057839522461185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180248988843371893014974123 270373483265057839522461185)
  ·
    refine ⟨202780112448793379641845889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 270373483265057839522461185 202780112448793379641845889)
    ·
      refine ⟨152085084336595034731384417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 202780112448793379641845889 152085084336595034731384417)
      ·
        refine ⟨114063813252446276048538313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 152085084336595034731384417 114063813252446276048538313)
        ·
          refine ⟨85547859939334707036403735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114063813252446276048538313 85547859939334707036403735)
          ·
            refine ⟨128321789909002060554605603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85547859939334707036403735 128321789909002060554605603)
            ·
              refine ⟨192482684863503090831908405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 128321789909002060554605603 192482684863503090831908405)
              ·
                refine ⟨18045251705953414765491413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 192482684863503090831908405 18045251705953414765491413)
                ·
                  refine ⟨422935586858283158566205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18045251705953414765491413 422935586858283158566205)
                  ·
                    rfl

theorem cell23_7412977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 5, 7].length) (baseStart_7412977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7412977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7412977 prefixEnd_7412977 := by exact prefixLift 7412977
  have htrace : WordTrace (prefixWord ++ tailWord_7412977) baseStart_7412977 baseEnd_7412977 := by
    simpa [prefixWord, tailWord_7412977, baseEnd_7412977] using wordTrace_append hprefix tailTrace_7412977
  have hstable : (prefixWord ++ tailWord_7412977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7412977).length < 2 ^ (prefixWord ++ tailWord_7412977).sum := by decide
  have hdescent : baseEnd_7412977 < baseStart_7412977 := by decide
  rcases family_descends (prefixWord ++ tailWord_7412977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7412988 : List Nat := [2, 2, 2, 1, 5, 1, 2, 1, 1, 4, 2]
def baseStart_7412988 : Nat := 118140960795 + 7412988 * 2 ^ 59
def prefixEnd_7412988 : Nat := 4983230072969 + 3 ^ 40 * 7412988 * 2
def baseEnd_7412988 : Nat := 3806425930011747884058295

theorem tailTrace_7412988 : CollatzResearch.WordTrace tailWord_7412988 prefixEnd_7412988 3806425930011747884058295 := by
  unfold tailWord_7412988
  simp only [CollatzResearch.WordTrace]
  refine ⟨135186942234008994200555809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180249256312011992267407745 135186942234008994200555809)
  ·
    refine ⟨101390206675506745650416857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135186942234008994200555809 101390206675506745650416857)
    ·
      refine ⟨76042655006630059237812643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101390206675506745650416857 76042655006630059237812643)
      ·
        refine ⟨114063982509945088856718965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76042655006630059237812643 114063982509945088856718965)
        ·
          refine ⟨10693498360307352080317403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 114063982509945088856718965 10693498360307352080317403)
          ·
            refine ⟨16040247540461028120476105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10693498360307352080317403 16040247540461028120476105)
            ·
              refine ⟨12030185655345771090357079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16040247540461028120476105 12030185655345771090357079)
              ·
                refine ⟨18045278483018656635535619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12030185655345771090357079 18045278483018656635535619)
                ·
                  refine ⟨27067917724527984953303429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18045278483018656635535619 27067917724527984953303429)
                  ·
                    refine ⟨5075234573348997178744393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27067917724527984953303429 5075234573348997178744393)
                    ·
                      refine ⟨3806425930011747884058295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5075234573348997178744393 3806425930011747884058295)
                      ·
                        rfl

theorem cell23_7412988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 2, 1, 1, 4, 2].length) (baseStart_7412988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7412988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7412988 prefixEnd_7412988 := by exact prefixLift 7412988
  have htrace : WordTrace (prefixWord ++ tailWord_7412988) baseStart_7412988 baseEnd_7412988 := by
    simpa [prefixWord, tailWord_7412988, baseEnd_7412988] using wordTrace_append hprefix tailTrace_7412988
  have hstable : (prefixWord ++ tailWord_7412988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7412988).length < 2 ^ (prefixWord ++ tailWord_7412988).sum := by decide
  have hdescent : baseEnd_7412988 < baseStart_7412988 := by decide
  rcases family_descends (prefixWord ++ tailWord_7412988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7413021 : List Nat := [1, 4, 2, 3, 1, 1, 1, 2, 2, 3, 3]
def baseStart_7413021 : Nat := 118140960795 + 7413021 * 2 ^ 59
def prefixEnd_7413021 : Nat := 4983230072969 + 3 ^ 40 * 7413021 * 2
def baseEnd_7413021 : Nat := 3806442874873346254945643

theorem tailTrace_7413021 : CollatzResearch.WordTrace tailWord_7413021 prefixEnd_7413021 3806442874873346254945643 := by
  unfold tailWord_7413021
  simp only [CollatzResearch.WordTrace]
  refine ⟨270375088076898435037062917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180250058717932290024708611 270375088076898435037062917)
  ·
    refine ⟨50695329014418456569449297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 270375088076898435037062917 50695329014418456569449297)
    ·
      refine ⟨38021496760813842427086973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50695329014418456569449297 38021496760813842427086973)
      ·
        refine ⟨14258061285305190910157615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38021496760813842427086973 14258061285305190910157615)
        ·
          refine ⟨21387091927957786365236423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14258061285305190910157615 21387091927957786365236423)
          ·
            refine ⟨32080637891936679547854635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21387091927957786365236423 32080637891936679547854635)
            ·
              refine ⟨48120956837905019321781953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32080637891936679547854635 48120956837905019321781953)
              ·
                refine ⟨36090717628428764491336465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48120956837905019321781953 36090717628428764491336465)
                ·
                  refine ⟨27068038221321573368502349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36090717628428764491336465 27068038221321573368502349)
                  ·
                    refine ⟨10150514332995590013188381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27068038221321573368502349 10150514332995590013188381)
                    ·
                      refine ⟨3806442874873346254945643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10150514332995590013188381 3806442874873346254945643)
                      ·
                        rfl

theorem cell23_7413021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 1, 2, 2, 3, 3].length) (baseStart_7413021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7413021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7413021 prefixEnd_7413021 := by exact prefixLift 7413021
  have htrace : WordTrace (prefixWord ++ tailWord_7413021) baseStart_7413021 baseEnd_7413021 := by
    simpa [prefixWord, tailWord_7413021, baseEnd_7413021] using wordTrace_append hprefix tailTrace_7413021
  have hstable : (prefixWord ++ tailWord_7413021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7413021).length < 2 ^ (prefixWord ++ tailWord_7413021).sum := by decide
  have hdescent : baseEnd_7413021 < baseStart_7413021 := by decide
  rcases family_descends (prefixWord ++ tailWord_7413021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7413022 : List Nat := [4, 3, 2, 1, 2, 1, 1, 1, 4, 2, 2]
def baseStart_7413022 : Nat := 118140960795 + 7413022 * 2 ^ 59
def prefixEnd_7413022 : Nat := 4983230072969 + 3 ^ 40 * 7413022 * 2
def baseEnd_7413022 : Nat := 3806443388354000751033139

theorem tailTrace_7413022 : CollatzResearch.WordTrace tailWord_7413022 prefixEnd_7413022 3806443388354000751033139 := by
  unfold tailWord_7413022
  simp only [CollatzResearch.WordTrace]
  refine ⟨33796890568736851525981165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 180250083033263208138566213 33796890568736851525981165)
  ·
    refine ⟨12673833963276319322242937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33796890568736851525981165 12673833963276319322242937)
    ·
      refine ⟨9505375472457239491682203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12673833963276319322242937 9505375472457239491682203)
      ·
        refine ⟨14258063208685859237523305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9505375472457239491682203 14258063208685859237523305)
        ·
          refine ⟨10693547406514394428142479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14258063208685859237523305 10693547406514394428142479)
          ·
            refine ⟨16040321109771591642213719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10693547406514394428142479 16040321109771591642213719)
            ·
              refine ⟨24060481664657387463320579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16040321109771591642213719 24060481664657387463320579)
              ·
                refine ⟨36090722496986081194980869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24060481664657387463320579 36090722496986081194980869)
                ·
                  refine ⟨6767010468184890224058913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36090722496986081194980869 6767010468184890224058913)
                  ·
                    refine ⟨5075257851138667668044185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6767010468184890224058913 5075257851138667668044185)
                    ·
                      refine ⟨3806443388354000751033139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5075257851138667668044185 3806443388354000751033139)
                      ·
                        rfl

theorem cell23_7413022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 1, 1, 4, 2, 2].length) (baseStart_7413022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7413022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7413022 prefixEnd_7413022 := by exact prefixLift 7413022
  have htrace : WordTrace (prefixWord ++ tailWord_7413022) baseStart_7413022 baseEnd_7413022 := by
    simpa [prefixWord, tailWord_7413022, baseEnd_7413022] using wordTrace_append hprefix tailTrace_7413022
  have hstable : (prefixWord ++ tailWord_7413022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7413022).length < 2 ^ (prefixWord ++ tailWord_7413022).sum := by decide
  have hdescent : baseEnd_7413022 < baseStart_7413022 := by decide
  rcases family_descends (prefixWord ++ tailWord_7413022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7413054 : List Nat := [4, 2, 1, 2, 1, 1, 1, 1, 2, 8]
def baseStart_7413054 : Nat := 118140960795 + 7413054 * 2 ^ 59
def prefixEnd_7413054 : Nat := 4983230072969 + 3 ^ 40 * 7413054 * 2
def baseEnd_7413054 : Nat := 1268819939911648208610997

theorem tailTrace_7413054 : CollatzResearch.WordTrace tailWord_7413054 prefixEnd_7413054 1268819939911648208610997 := by
  unfold tailWord_7413054
  simp only [CollatzResearch.WordTrace]
  refine ⟨33797036460722360209126777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 180250861123852587782009477 33797036460722360209126777)
  ·
    refine ⟨25347777345541770156845083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33797036460722360209126777 25347777345541770156845083)
    ·
      refine ⟨38021666018312655235267625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25347777345541770156845083 38021666018312655235267625)
      ·
        refine ⟨28516249513734491426450719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38021666018312655235267625 28516249513734491426450719)
        ·
          refine ⟨42774374270601737139676079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28516249513734491426450719 42774374270601737139676079)
          ·
            refine ⟨64161561405902605709514119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42774374270601737139676079 64161561405902605709514119)
            ·
              refine ⟨96242342108853908564271179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64161561405902605709514119 96242342108853908564271179)
              ·
                refine ⟨144363513163280862846406769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 96242342108853908564271179 144363513163280862846406769)
                ·
                  refine ⟨108272634872460647134805077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 144363513163280862846406769 108272634872460647134805077)
                  ·
                    refine ⟨1268819939911648208610997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 108272634872460647134805077 1268819939911648208610997)
                    ·
                      rfl

theorem cell23_7413054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 1, 2, 8].length) (baseStart_7413054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7413054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7413054 prefixEnd_7413054 := by exact prefixLift 7413054
  have htrace : WordTrace (prefixWord ++ tailWord_7413054) baseStart_7413054 baseEnd_7413054 := by
    simpa [prefixWord, tailWord_7413054, baseEnd_7413054] using wordTrace_append hprefix tailTrace_7413054
  have hstable : (prefixWord ++ tailWord_7413054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7413054).length < 2 ^ (prefixWord ++ tailWord_7413054).sum := by decide
  have hdescent : baseEnd_7413054 < baseStart_7413054 := by decide
  rcases family_descends (prefixWord ++ tailWord_7413054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7413085 : List Nat := [1, 4, 5, 1, 1, 1, 1, 1, 1, 2, 5]
def baseStart_7413085 : Nat := 118140960795 + 7413085 * 2 ^ 59
def prefixEnd_7413085 : Nat := 4983230072969 + 3 ^ 40 * 7413085 * 2
def baseEnd_7413085 : Nat := 3806475737635234004545349

theorem tailTrace_7413085 : CollatzResearch.WordTrace tailWord_7413085 prefixEnd_7413085 3806475737635234004545349 := by
  unfold tailWord_7413085
  simp only [CollatzResearch.WordTrace]
  refine ⟨270377422348666573967392709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180251614899111049311595139 270377422348666573967392709)
  ·
    refine ⟨50695766690374982618886133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 270377422348666573967392709 50695766690374982618886133)
    ·
      refine ⟨4752728127222654620520575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 50695766690374982618886133 4752728127222654620520575)
      ·
        refine ⟨7129092190833981930780863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4752728127222654620520575 7129092190833981930780863)
        ·
          refine ⟨10693638286250972896171295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7129092190833981930780863 10693638286250972896171295)
          ·
            refine ⟨16040457429376459344256943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10693638286250972896171295 16040457429376459344256943)
            ·
              refine ⟨24060686144064689016385415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16040457429376459344256943 24060686144064689016385415)
              ·
                refine ⟨36091029216097033524578123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24060686144064689016385415 36091029216097033524578123)
                ·
                  refine ⟨54136543824145550286867185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36091029216097033524578123 54136543824145550286867185)
                  ·
                    refine ⟨40602407868109162715150389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 54136543824145550286867185 40602407868109162715150389)
                    ·
                      refine ⟨3806475737635234004545349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40602407868109162715150389 3806475737635234004545349)
                      ·
                        rfl

theorem cell23_7413085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 1, 1, 1, 2, 5].length) (baseStart_7413085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7413085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7413085 prefixEnd_7413085 := by exact prefixLift 7413085
  have htrace : WordTrace (prefixWord ++ tailWord_7413085) baseStart_7413085 baseEnd_7413085 := by
    simpa [prefixWord, tailWord_7413085, baseEnd_7413085] using wordTrace_append hprefix tailTrace_7413085
  have hstable : (prefixWord ++ tailWord_7413085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7413085).length < 2 ^ (prefixWord ++ tailWord_7413085).sum := by decide
  have hdescent : baseEnd_7413085 < baseStart_7413085 := by decide
  rcases family_descends (prefixWord ++ tailWord_7413085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7413088 : List Nat := [2, 1, 1, 3, 4, 3, 1, 1, 3, 4]
def baseStart_7413088 : Nat := 118140960795 + 7413088 * 2 ^ 59
def prefixEnd_7413088 : Nat := 4983230072969 + 3 ^ 40 * 7413088 * 2
def baseEnd_7413088 : Nat := 1268825759359065830935945

theorem tailTrace_7413088 : CollatzResearch.WordTrace tailWord_7413088 prefixEnd_7413088 1268825759359065830935945 := by
  unfold tailWord_7413088
  simp only [CollatzResearch.WordTrace]
  refine ⟨135188765883827852739875959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180251687845103803653167945 135188765883827852739875959)
  ·
    refine ⟨202783148825741779109813939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135188765883827852739875959 202783148825741779109813939)
    ·
      refine ⟨304174723238612668664720909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202783148825741779109813939 304174723238612668664720909)
      ·
        refine ⟨114065521214479750749270341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 304174723238612668664720909 114065521214479750749270341)
        ·
          refine ⟨21387285227714953265488189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 114065521214479750749270341 21387285227714953265488189)
          ·
            refine ⟨8020231960393107474558071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21387285227714953265488189 8020231960393107474558071)
            ·
              refine ⟨12030347940589661211837107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8020231960393107474558071 12030347940589661211837107)
              ·
                refine ⟨18045521910884491817755661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12030347940589661211837107 18045521910884491817755661)
                ·
                  refine ⟨6767070716581684431658373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18045521910884491817755661 6767070716581684431658373)
                  ·
                    refine ⟨1268825759359065830935945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6767070716581684431658373 1268825759359065830935945)
                    ·
                      rfl

theorem cell23_7413088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 3, 1, 1, 3, 4].length) (baseStart_7413088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7413088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7413088 prefixEnd_7413088 := by exact prefixLift 7413088
  have htrace : WordTrace (prefixWord ++ tailWord_7413088) baseStart_7413088 baseEnd_7413088 := by
    simpa [prefixWord, tailWord_7413088, baseEnd_7413088] using wordTrace_append hprefix tailTrace_7413088
  have hstable : (prefixWord ++ tailWord_7413088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7413088).length < 2 ^ (prefixWord ++ tailWord_7413088).sum := by decide
  have hdescent : baseEnd_7413088 < baseStart_7413088 := by decide
  rcases family_descends (prefixWord ++ tailWord_7413088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7413101 : List Nat := [1, 5, 1, 1, 1, 4, 1, 3, 6]
def baseStart_7413101 : Nat := 118140960795 + 7413101 * 2 ^ 59
def prefixEnd_7413101 : Nat := 4983230072969 + 3 ^ 40 * 7413101 * 2
def baseEnd_7413101 : Nat := 422942661480633993549475

theorem tailTrace_7413101 : CollatzResearch.WordTrace tailWord_7413101 prefixEnd_7413101 422942661480633993549475 := by
  unfold tailWord_7413101
  simp only [CollatzResearch.WordTrace]
  refine ⟨270378005916608608699975157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180252003944405739133316771 270378005916608608699975157)
  ·
    refine ⟨25347938054682057065622671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 270378005916608608699975157 25347938054682057065622671)
    ·
      refine ⟨38021907082023085598434007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25347938054682057065622671 38021907082023085598434007)
      ·
        refine ⟨57032860623034628397651011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38021907082023085598434007 57032860623034628397651011)
        ·
          refine ⟨85549290934551942596476517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57032860623034628397651011 85549290934551942596476517)
          ·
            refine ⟨16040492050228489236839347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 85549290934551942596476517 16040492050228489236839347)
            ·
              refine ⟨24060738075342733855259021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16040492050228489236839347 24060738075342733855259021)
              ·
                refine ⟨9022776778253525195722133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24060738075342733855259021 9022776778253525195722133)
                ·
                  refine ⟨422942661480633993549475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9022776778253525195722133 422942661480633993549475)
                  ·
                    rfl

theorem cell23_7413101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 1, 3, 6].length) (baseStart_7413101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7413101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7413101 prefixEnd_7413101 := by exact prefixLift 7413101
  have htrace : WordTrace (prefixWord ++ tailWord_7413101) baseStart_7413101 baseEnd_7413101 := by
    simpa [prefixWord, tailWord_7413101, baseEnd_7413101] using wordTrace_append hprefix tailTrace_7413101
  have hstable : (prefixWord ++ tailWord_7413101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7413101).length < 2 ^ (prefixWord ++ tailWord_7413101).sum := by decide
  have hdescent : baseEnd_7413101 < baseStart_7413101 := by decide
  rcases family_descends (prefixWord ++ tailWord_7413101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7413111 : List Nat := [1, 1, 3, 1, 1, 2, 4, 1, 5, 1, 3]
def baseStart_7413111 : Nat := 118140960795 + 7413111 * 2 ^ 59
def prefixEnd_7413111 : Nat := 4983230072969 + 3 ^ 40 * 7413111 * 2
def baseEnd_7413111 : Nat := 3806489088132250902820229

theorem tailTrace_7413111 : CollatzResearch.WordTrace tailWord_7413111 prefixEnd_7413111 3806489088132250902820229 := by
  unfold tailWord_7413111
  simp only [CollatzResearch.WordTrace]
  refine ⟨270378370646572380407839187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180252247097714920271892791 270378370646572380407839187)
  ·
    refine ⟨405567555969858570611758781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270378370646572380407839187 405567555969858570611758781)
    ·
      refine ⟨152087833488696963979409543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 405567555969858570611758781 152087833488696963979409543)
      ·
        refine ⟨228131750233045445969114315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152087833488696963979409543 228131750233045445969114315)
        ·
          refine ⟨342197625349568168953671473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 228131750233045445969114315 342197625349568168953671473)
          ·
            refine ⟨256648219012176126715253605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 342197625349568168953671473 256648219012176126715253605)
            ·
              refine ⟨48121541064783023759110051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 256648219012176126715253605 48121541064783023759110051)
              ·
                refine ⟨72182311597174535638665077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48121541064783023759110051 72182311597174535638665077)
                ·
                  refine ⟨6767091712235112716124851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 72182311597174535638665077 6767091712235112716124851)
                  ·
                    refine ⟨10150637568352669074187277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6767091712235112716124851 10150637568352669074187277)
                    ·
                      refine ⟨3806489088132250902820229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10150637568352669074187277 3806489088132250902820229)
                      ·
                        rfl

theorem cell23_7413111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 4, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 4, 1, 5, 1, 3].length) (baseStart_7413111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7413111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7413111 prefixEnd_7413111 := by exact prefixLift 7413111
  have htrace : WordTrace (prefixWord ++ tailWord_7413111) baseStart_7413111 baseEnd_7413111 := by
    simpa [prefixWord, tailWord_7413111, baseEnd_7413111] using wordTrace_append hprefix tailTrace_7413111
  have hstable : (prefixWord ++ tailWord_7413111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7413111).length < 2 ^ (prefixWord ++ tailWord_7413111).sum := by decide
  have hdescent : baseEnd_7413111 < baseStart_7413111 := by decide
  rcases family_descends (prefixWord ++ tailWord_7413111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7413114 : List Nat := [3, 1, 1, 1, 1, 1, 2, 5, 3, 5]
def baseStart_7413114 : Nat := 118140960795 + 7413114 * 2 ^ 59
def prefixEnd_7413114 : Nat := 4983230072969 + 3 ^ 40 * 7413114 * 2
def baseEnd_7413114 : Nat := 1268830209524738130360905

theorem tailTrace_7413114 : CollatzResearch.WordTrace tailWord_7413114 prefixEnd_7413114 1268830209524738130360905 := by
  unfold tailWord_7413114
  simp only [CollatzResearch.WordTrace]
  refine ⟨67594620016390377980049599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 180252320043707674613465597 67594620016390377980049599)
  ·
    refine ⟨101391930024585566970074399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67594620016390377980049599 101391930024585566970074399)
    ·
      refine ⟨152087895036878350455111599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101391930024585566970074399 152087895036878350455111599)
      ·
        refine ⟨228131842555317525682667399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152087895036878350455111599 228131842555317525682667399)
        ·
          refine ⟨342197763832976288524001099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 228131842555317525682667399 342197763832976288524001099)
          ·
            refine ⟨513296645749464432786001649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 342197763832976288524001099 513296645749464432786001649)
            ·
              refine ⟨384972484312098324589501237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 513296645749464432786001649 384972484312098324589501237)
              ·
                refine ⟨36091170404259217930265741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 384972484312098324589501237 36091170404259217930265741)
                ·
                  refine ⟨13534188901597206723849653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36091170404259217930265741 13534188901597206723849653)
                  ·
                    refine ⟨1268830209524738130360905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13534188901597206723849653 1268830209524738130360905)
                    ·
                      rfl

theorem cell23_7413114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 5, 3, 5].length) (baseStart_7413114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7413114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7413114 prefixEnd_7413114 := by exact prefixLift 7413114
  have htrace : WordTrace (prefixWord ++ tailWord_7413114) baseStart_7413114 baseEnd_7413114 := by
    simpa [prefixWord, tailWord_7413114, baseEnd_7413114] using wordTrace_append hprefix tailTrace_7413114
  have hstable : (prefixWord ++ tailWord_7413114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7413114).length < 2 ^ (prefixWord ++ tailWord_7413114).sum := by decide
  have hdescent : baseEnd_7413114 < baseStart_7413114 := by decide
  rcases family_descends (prefixWord ++ tailWord_7413114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7413145 : List Nat := [1, 2, 1, 2, 1, 6, 1, 4, 1, 1, 3]
def baseStart_7413145 : Nat := 118140960795 + 7413145 * 2 ^ 59
def prefixEnd_7413145 : Nat := 4983230072969 + 3 ^ 40 * 7413145 * 2
def baseEnd_7413145 : Nat := 3806506546474503769795073

theorem tailTrace_7413145 : CollatzResearch.WordTrace tailWord_7413145 prefixEnd_7413145 3806506546474503769795073 := by
  unfold tailWord_7413145
  simp only [CollatzResearch.WordTrace]
  refine ⟨270379610728449204214576889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180253073818966136143051259 270379610728449204214576889)
  ·
    refine ⟨202784708046336903160932667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 270379610728449204214576889 202784708046336903160932667)
    ·
      refine ⟨304177062069505354741399001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202784708046336903160932667 304177062069505354741399001)
      ·
        refine ⟨228132796552129016056049251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 304177062069505354741399001 228132796552129016056049251)
        ·
          refine ⟨342199194828193524084073877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 228132796552129016056049251 342199194828193524084073877)
          ·
            refine ⟨16040587257571571441440963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 342199194828193524084073877 16040587257571571441440963)
            ·
              refine ⟨24060880886357357162161445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16040587257571571441440963 24060880886357357162161445)
              ·
                refine ⟨4511415166192004467905271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24060880886357357162161445 4511415166192004467905271)
                ·
                  refine ⟨6767122749288006701857907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4511415166192004467905271 6767122749288006701857907)
                  ·
                    refine ⟨10150684123932010052786861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6767122749288006701857907 10150684123932010052786861)
                    ·
                      refine ⟨3806506546474503769795073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10150684123932010052786861 3806506546474503769795073)
                      ·
                        rfl

theorem cell23_7413145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 1, 4, 1, 1, 3].length) (baseStart_7413145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7413145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7413145 prefixEnd_7413145 := by exact prefixLift 7413145
  have htrace : WordTrace (prefixWord ++ tailWord_7413145) baseStart_7413145 baseEnd_7413145 := by
    simpa [prefixWord, tailWord_7413145, baseEnd_7413145] using wordTrace_append hprefix tailTrace_7413145
  have hstable : (prefixWord ++ tailWord_7413145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7413145).length < 2 ^ (prefixWord ++ tailWord_7413145).sum := by decide
  have hdescent : baseEnd_7413145 < baseStart_7413145 := by decide
  rcases family_descends (prefixWord ++ tailWord_7413145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7413151 : List Nat := [1, 1, 2, 5, 1, 2, 1, 2, 3, 1, 4]
def baseStart_7413151 : Nat := 118140960795 + 7413151 * 2 ^ 59
def prefixEnd_7413151 : Nat := 4983230072969 + 3 ^ 40 * 7413151 * 2
def baseEnd_7413151 : Nat := 3806509627358430746320045

theorem tailTrace_7413151 : CollatzResearch.WordTrace tailWord_7413151 prefixEnd_7413151 3806509627358430746320045 := by
  unfold tailWord_7413151
  simp only [CollatzResearch.WordTrace]
  refine ⟨270379829566427467239295307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180253219710951644826196871 270379829566427467239295307)
  ·
    refine ⟨405569744349641200858942961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270379829566427467239295307 405569744349641200858942961)
    ·
      refine ⟨304177308262230900644207221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 405569744349641200858942961 304177308262230900644207221)
      ·
        refine ⟨28516622649584146935394427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 304177308262230900644207221 28516622649584146935394427)
        ·
          refine ⟨42774933974376220403091641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28516622649584146935394427 42774933974376220403091641)
          ·
            refine ⟨32081200480782165302318731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42774933974376220403091641 32081200480782165302318731)
            ·
              refine ⟨48121800721173247953478097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32081200480782165302318731 48121800721173247953478097)
              ·
                refine ⟨36091350540879935965108573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48121800721173247953478097 36091350540879935965108573)
                ·
                  refine ⟨13534256452829975986915715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36091350540879935965108573 13534256452829975986915715)
                  ·
                    refine ⟨20301384679244963980373573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13534256452829975986915715 20301384679244963980373573)
                    ·
                      refine ⟨3806509627358430746320045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20301384679244963980373573 3806509627358430746320045)
                      ·
                        rfl

theorem cell23_7413151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 1, 2, 3, 1, 4].length) (baseStart_7413151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7413151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7413151 prefixEnd_7413151 := by exact prefixLift 7413151
  have htrace : WordTrace (prefixWord ++ tailWord_7413151) baseStart_7413151 baseEnd_7413151 := by
    simpa [prefixWord, tailWord_7413151, baseEnd_7413151] using wordTrace_append hprefix tailTrace_7413151
  have hstable : (prefixWord ++ tailWord_7413151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7413151).length < 2 ^ (prefixWord ++ tailWord_7413151).sum := by decide
  have hdescent : baseEnd_7413151 < baseStart_7413151 := by decide
  rcases family_descends (prefixWord ++ tailWord_7413151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7413164 : List Nat := [2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 6]
def baseStart_7413164 : Nat := 118140960795 + 7413164 * 2 ^ 59
def prefixEnd_7413164 : Nat := 4983230072969 + 3 ^ 40 * 7413164 * 2
def baseEnd_7413164 : Nat := 3806516302606939195457485

theorem tailTrace_7413164 : CollatzResearch.WordTrace tailWord_7413164 prefixEnd_7413164 3806516302606939195457485 := by
  unfold tailWord_7413164
  simp only [CollatzResearch.WordTrace]
  refine ⟨135190151857690185229759273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180253535810253580306345697 135190151857690185229759273)
  ·
    refine ⟨101392613893267638922319455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135190151857690185229759273 101392613893267638922319455)
    ·
      refine ⟨152088920839901458383479183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101392613893267638922319455 152088920839901458383479183)
      ·
        refine ⟨228133381259852187575218775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152088920839901458383479183 228133381259852187575218775)
        ·
          refine ⟨342200071889778281362828163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 228133381259852187575218775 342200071889778281362828163)
          ·
            refine ⟨513300107834667422044242245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 342200071889778281362828163 513300107834667422044242245)
            ·
              refine ⟨96243770219000141633295421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 513300107834667422044242245 96243770219000141633295421)
              ·
                refine ⟨36091413832125053112485783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 96243770219000141633295421 36091413832125053112485783)
                ·
                  refine ⟨54137120748187579668728675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36091413832125053112485783 54137120748187579668728675)
                  ·
                    refine ⟨81205681122281369503093013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 54137120748187579668728675 81205681122281369503093013)
                    ·
                      refine ⟨3806516302606939195457485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 81205681122281369503093013 3806516302606939195457485)
                      ·
                        rfl

theorem cell23_7413164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 6].length) (baseStart_7413164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7413164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7413164 prefixEnd_7413164 := by exact prefixLift 7413164
  have htrace : WordTrace (prefixWord ++ tailWord_7413164) baseStart_7413164 baseEnd_7413164 := by
    simpa [prefixWord, tailWord_7413164, baseEnd_7413164] using wordTrace_append hprefix tailTrace_7413164
  have hstable : (prefixWord ++ tailWord_7413164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7413164).length < 2 ^ (prefixWord ++ tailWord_7413164).sum := by decide
  have hdescent : baseEnd_7413164 < baseStart_7413164 := by decide
  rcases family_descends (prefixWord ++ tailWord_7413164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7413181 : List Nat := [1, 4, 1, 2, 2, 1, 1, 4, 1, 2, 4]
def baseStart_7413181 : Nat := 118140960795 + 7413181 * 2 ^ 59
def prefixEnd_7413181 : Nat := 4983230072969 + 3 ^ 40 * 7413181 * 2
def baseEnd_7413181 : Nat := 3806525031778065628944907

theorem tailTrace_7413181 : CollatzResearch.WordTrace tailWord_7413181 prefixEnd_7413181 3806525031778065628944907 := by
  unfold tailWord_7413181
  simp only [CollatzResearch.WordTrace]
  refine ⟨270380923756318782362887397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180253949170879188241924931 270380923756318782362887397)
  ·
    refine ⟨50696423204309771693041387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 270380923756318782362887397 50696423204309771693041387)
    ·
      refine ⟨76044634806464657539562081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50696423204309771693041387 76044634806464657539562081)
      ·
        refine ⟨57033476104848493154671561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76044634806464657539562081 57033476104848493154671561)
        ·
          refine ⟨42775107078636369866003671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57033476104848493154671561 42775107078636369866003671)
          ·
            refine ⟨64162660617954554799005507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42775107078636369866003671 64162660617954554799005507)
            ·
              refine ⟨96243990926931832198508261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64162660617954554799005507 96243990926931832198508261)
              ·
                refine ⟨18045748298799718537220299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 96243990926931832198508261 18045748298799718537220299)
                ·
                  refine ⟨27068622448199577805830449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18045748298799718537220299 27068622448199577805830449)
                  ·
                    refine ⟨20301466836149683354372837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27068622448199577805830449 20301466836149683354372837)
                    ·
                      refine ⟨3806525031778065628944907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20301466836149683354372837 3806525031778065628944907)
                      ·
                        rfl

theorem cell23_7413181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 4, 1, 2, 4].length) (baseStart_7413181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7413181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7413181 prefixEnd_7413181 := by exact prefixLift 7413181
  have htrace : WordTrace (prefixWord ++ tailWord_7413181) baseStart_7413181 baseEnd_7413181 := by
    simpa [prefixWord, tailWord_7413181, baseEnd_7413181] using wordTrace_append hprefix tailTrace_7413181
  have hstable : (prefixWord ++ tailWord_7413181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7413181).length < 2 ^ (prefixWord ++ tailWord_7413181).sum := by decide
  have hdescent : baseEnd_7413181 < baseStart_7413181 := by decide
  rcases family_descends (prefixWord ++ tailWord_7413181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7413186 : List Nat := [3, 5, 2, 1, 2, 1, 1, 2, 6]
def baseStart_7413186 : Nat := 118140960795 + 7413186 * 2 ^ 59
def prefixEnd_7413186 : Nat := 4983230072969 + 3 ^ 40 * 7413186 * 2
def baseEnd_7413186 : Nat := 422947511020148678820265

theorem tailTrace_7413186 : CollatzResearch.WordTrace tailWord_7413186 prefixEnd_7413186 422947511020148678820265 := by
  unfold tailWord_7413186
  simp only [CollatzResearch.WordTrace]
  refine ⟨67595276530325167054204853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 180254070747533778811212941 67595276530325167054204853)
  ·
    refine ⟨6337057174717984411331705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 67595276530325167054204853 6337057174717984411331705)
    ·
      refine ⟨4752792881038488308498779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6337057174717984411331705 4752792881038488308498779)
      ·
        refine ⟨7129189321557732462748169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4752792881038488308498779 7129189321557732462748169)
        ·
          refine ⟨5346891991168299347061127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7129189321557732462748169 5346891991168299347061127)
          ·
            refine ⟨8020337986752449020591691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5346891991168299347061127 8020337986752449020591691)
            ·
              refine ⟨12030506980128673530887537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8020337986752449020591691 12030506980128673530887537)
              ·
                refine ⟨9022880235096505148165653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12030506980128673530887537 9022880235096505148165653)
                ·
                  refine ⟨422947511020148678820265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9022880235096505148165653 422947511020148678820265)
                  ·
                    rfl

theorem cell23_7413186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 2, 1, 1, 2, 6].length) (baseStart_7413186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7413186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7413186 prefixEnd_7413186 := by exact prefixLift 7413186
  have htrace : WordTrace (prefixWord ++ tailWord_7413186) baseStart_7413186 baseEnd_7413186 := by
    simpa [prefixWord, tailWord_7413186, baseEnd_7413186] using wordTrace_append hprefix tailTrace_7413186
  have hstable : (prefixWord ++ tailWord_7413186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7413186).length < 2 ^ (prefixWord ++ tailWord_7413186).sum := by decide
  have hdescent : baseEnd_7413186 < baseStart_7413186 := by decide
  rcases family_descends (prefixWord ++ tailWord_7413186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7413245 : List Nat := [1, 4, 1, 1, 1, 4, 2, 3, 1, 3, 2]
def baseStart_7413245 : Nat := 118140960795 + 7413245 * 2 ^ 59
def prefixEnd_7413245 : Nat := 4983230072969 + 3 ^ 40 * 7413245 * 2
def baseEnd_7413245 : Nat := 3806557894539953378544613

theorem tailTrace_7413245 : CollatzResearch.WordTrace tailWord_7413245 prefixEnd_7413245 3806557894539953378544613 := by
  unfold tailWord_7413245
  simp only [CollatzResearch.WordTrace]
  refine ⟨270383258028086921293217189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180255505352057947528811459 270383258028086921293217189)
  ·
    refine ⟨50696860880266297742478223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 270383258028086921293217189 50696860880266297742478223)
    ·
      refine ⟨76045291320399446613717335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50696860880266297742478223 76045291320399446613717335)
      ·
        refine ⟨114067936980599169920576003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76045291320399446613717335 114067936980599169920576003)
        ·
          refine ⟨171101905470898754880864005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114067936980599169920576003 171101905470898754880864005)
          ·
            refine ⟨32081607275793516540162001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 171101905470898754880864005 32081607275793516540162001)
            ·
              refine ⟨24061205456845137405121501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32081607275793516540162001 24061205456845137405121501)
              ·
                refine ⟨9022952046316926526920563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24061205456845137405121501 9022952046316926526920563)
                ·
                  refine ⟨13534428069475389790380845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9022952046316926526920563 13534428069475389790380845)
                  ·
                    refine ⟨5075410526053271171392817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13534428069475389790380845 5075410526053271171392817)
                    ·
                      refine ⟨3806557894539953378544613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5075410526053271171392817 3806557894539953378544613)
                      ·
                        rfl

theorem cell23_7413245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 2, 3, 1, 3, 2].length) (baseStart_7413245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7413245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7413245 prefixEnd_7413245 := by exact prefixLift 7413245
  have htrace : WordTrace (prefixWord ++ tailWord_7413245) baseStart_7413245 baseEnd_7413245 := by
    simpa [prefixWord, tailWord_7413245, baseEnd_7413245] using wordTrace_append hprefix tailTrace_7413245
  have hstable : (prefixWord ++ tailWord_7413245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7413245).length < 2 ^ (prefixWord ++ tailWord_7413245).sum := by decide
  have hdescent : baseEnd_7413245 < baseStart_7413245 := by decide
  rcases family_descends (prefixWord ++ tailWord_7413245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7413291 : List Nat := [1, 1, 1, 1, 2, 1, 3, 1, 6, 3, 3]
def baseStart_7413291 : Nat := 118140960795 + 7413291 * 2 ^ 59
def prefixEnd_7413291 : Nat := 4983230072969 + 3 ^ 40 * 7413291 * 2
def baseEnd_7413291 : Nat := 3806581514650060198569401

theorem tailTrace_7413291 : CollatzResearch.WordTrace tailWord_7413291 prefixEnd_7413291 3806581514650060198569401 := by
  unfold tailWord_7413291
  simp only [CollatzResearch.WordTrace]
  refine ⟨270384935785920271149391727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180256623857280180766261151 270384935785920271149391727)
  ·
    refine ⟨405577403678880406724087591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270384935785920271149391727 405577403678880406724087591)
    ·
      refine ⟨608366105518320610086131387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 405577403678880406724087591 608366105518320610086131387)
      ·
        refine ⟨912549158277480915129197081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 608366105518320610086131387 912549158277480915129197081)
        ·
          refine ⟨684411868708110686346897811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 912549158277480915129197081 684411868708110686346897811)
          ·
            refine ⟨1026617803062166029520346717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 684411868708110686346897811 1026617803062166029520346717)
            ·
              refine ⟨384981676148312261070130019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1026617803062166029520346717 384981676148312261070130019)
              ·
                refine ⟨577472514222468391605195029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 384981676148312261070130019 577472514222468391605195029)
                ·
                  refine ⟨27069024104178205856493517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 577472514222468391605195029 27069024104178205856493517)
                  ·
                    refine ⟨10150884039066827196185069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27069024104178205856493517 10150884039066827196185069)
                    ·
                      refine ⟨3806581514650060198569401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10150884039066827196185069 3806581514650060198569401)
                      ·
                        rfl

theorem cell23_7413291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 1, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 1, 6, 3, 3].length) (baseStart_7413291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7413291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7413291 prefixEnd_7413291 := by exact prefixLift 7413291
  have htrace : WordTrace (prefixWord ++ tailWord_7413291) baseStart_7413291 baseEnd_7413291 := by
    simpa [prefixWord, tailWord_7413291, baseEnd_7413291] using wordTrace_append hprefix tailTrace_7413291
  have hstable : (prefixWord ++ tailWord_7413291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7413291).length < 2 ^ (prefixWord ++ tailWord_7413291).sum := by decide
  have hdescent : baseEnd_7413291 < baseStart_7413291 := by decide
  rcases family_descends (prefixWord ++ tailWord_7413291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7413298 : List Nat := [3, 2, 1, 1, 2, 1, 1, 7, 5]
def baseStart_7413298 : Nat := 118140960795 + 7413298 * 2 ^ 59
def prefixEnd_7413298 : Nat := 4983230072969 + 3 ^ 40 * 7413298 * 2
def baseEnd_7413298 : Nat := 422953901001626852353541

theorem tailTrace_7413298 : CollatzResearch.WordTrace tailWord_7413298 prefixEnd_7413298 422953901001626852353541 := by
  unfold tailWord_7413298
  simp only [CollatzResearch.WordTrace]
  refine ⟨67596297774223727836224137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 180256794064596607563264365 67596297774223727836224137)
  ·
    refine ⟨50697223330667795877168103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67596297774223727836224137 50697223330667795877168103)
    ·
      refine ⟨76045834996001693815752155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50697223330667795877168103 76045834996001693815752155)
      ·
        refine ⟨114068752494002540723628233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76045834996001693815752155 114068752494002540723628233)
        ·
          refine ⟨85551564370501905542721175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114068752494002540723628233 85551564370501905542721175)
          ·
            refine ⟨128327346555752858314081763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85551564370501905542721175 128327346555752858314081763)
            ·
              refine ⟨192491019833629287471122645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 128327346555752858314081763 192491019833629287471122645)
              ·
                refine ⟨4511508277350686425104437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 192491019833629287471122645 4511508277350686425104437)
                ·
                  refine ⟨422953901001626852353541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4511508277350686425104437 422953901001626852353541)
                  ·
                    rfl

theorem cell23_7413298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 7, 5].length) (baseStart_7413298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7413298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7413298 prefixEnd_7413298 := by exact prefixLift 7413298
  have htrace : WordTrace (prefixWord ++ tailWord_7413298) baseStart_7413298 baseEnd_7413298 := by
    simpa [prefixWord, tailWord_7413298, baseEnd_7413298] using wordTrace_append hprefix tailTrace_7413298
  have hstable : (prefixWord ++ tailWord_7413298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7413298).length < 2 ^ (prefixWord ++ tailWord_7413298).sum := by decide
  have hdescent : baseEnd_7413298 < baseStart_7413298 := by decide
  rcases family_descends (prefixWord ++ tailWord_7413298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7413309 : List Nat := [1, 4, 1, 3, 3, 1, 2, 2, 2, 2, 2]
def baseStart_7413309 : Nat := 118140960795 + 7413309 * 2 ^ 59
def prefixEnd_7413309 : Nat := 4983230072969 + 3 ^ 40 * 7413309 * 2
def baseEnd_7413309 : Nat := 3806590757301841128144319

theorem tailTrace_7413309 : CollatzResearch.WordTrace tailWord_7413309 prefixEnd_7413309 3806590757301841128144319 := by
  unfold tailWord_7413309
  simp only [CollatzResearch.WordTrace]
  refine ⟨270385592299855060223546981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180257061533236706815697987 270385592299855060223546981)
  ·
    refine ⟨50697298556222823791915059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 270385592299855060223546981 50697298556222823791915059)
    ·
      refine ⟨76045947834334235687872589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50697298556222823791915059 76045947834334235687872589)
      ·
        refine ⟨28517230437875338382952221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76045947834334235687872589 28517230437875338382952221)
        ·
          refine ⟨10693961414203251893607083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28517230437875338382952221 10693961414203251893607083)
          ·
            refine ⟨16040942121304877840410625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10693961414203251893607083 16040942121304877840410625)
            ·
              refine ⟨12030706590978658380307969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16040942121304877840410625 12030706590978658380307969)
              ·
                refine ⟨9023029943233993785230977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12030706590978658380307969 9023029943233993785230977)
                ·
                  refine ⟨6767272457425495338923233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9023029943233993785230977 6767272457425495338923233)
                  ·
                    refine ⟨5075454343069121504192425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6767272457425495338923233 5075454343069121504192425)
                    ·
                      refine ⟨3806590757301841128144319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5075454343069121504192425 3806590757301841128144319)
                      ·
                        rfl

theorem cell23_7413309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 2, 2, 2, 2, 2].length) (baseStart_7413309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7413309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7413309 prefixEnd_7413309 := by exact prefixLift 7413309
  have htrace : WordTrace (prefixWord ++ tailWord_7413309) baseStart_7413309 baseEnd_7413309 := by
    simpa [prefixWord, tailWord_7413309, baseEnd_7413309] using wordTrace_append hprefix tailTrace_7413309
  have hstable : (prefixWord ++ tailWord_7413309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7413309).length < 2 ^ (prefixWord ++ tailWord_7413309).sum := by decide
  have hdescent : baseEnd_7413309 < baseStart_7413309 := by decide
  rcases family_descends (prefixWord ++ tailWord_7413309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7413348 : List Nat := [2, 3, 1, 1, 2, 4, 1, 1, 1, 3, 4]
def baseStart_7413348 : Nat := 118140960795 + 7413348 * 2 ^ 59
def prefixEnd_7413348 : Nat := 4983230072969 + 3 ^ 40 * 7413348 * 2
def baseEnd_7413348 : Nat := 3806610783047366475556639

theorem tailTrace_7413348 : CollatzResearch.WordTrace tailWord_7413348 prefixEnd_7413348 3806610783047366475556639 := by
  unfold tailWord_7413348
  simp only [CollatzResearch.WordTrace]
  refine ⟨135193507373356884942108349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180258009831142513256144465 135193507373356884942108349)
  ·
    refine ⟨50697565265008831853290631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 135193507373356884942108349 50697565265008831853290631)
    ·
      refine ⟨76046347897513247779935947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50697565265008831853290631 76046347897513247779935947)
      ·
        refine ⟨114069521846269871669903921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76046347897513247779935947 114069521846269871669903921)
        ·
          refine ⟨85552141384702403752427941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114069521846269871669903921 85552141384702403752427941)
          ·
            refine ⟨16041026509631700703580239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 85552141384702403752427941 16041026509631700703580239)
            ·
              refine ⟨24061539764447551055370359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16041026509631700703580239 24061539764447551055370359)
              ·
                refine ⟨36092309646671326583055539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24061539764447551055370359 36092309646671326583055539)
                ·
                  refine ⟨54138464470006989874583309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36092309646671326583055539 54138464470006989874583309)
                  ·
                    refine ⟨20301924176252621202968741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 54138464470006989874583309 20301924176252621202968741)
                    ·
                      refine ⟨3806610783047366475556639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20301924176252621202968741 3806610783047366475556639)
                      ·
                        rfl

theorem cell23_7413348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 1, 1, 1, 3, 4].length) (baseStart_7413348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7413348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7413348 prefixEnd_7413348 := by exact prefixLift 7413348
  have htrace : WordTrace (prefixWord ++ tailWord_7413348) baseStart_7413348 baseEnd_7413348 := by
    simpa [prefixWord, tailWord_7413348, baseEnd_7413348] using wordTrace_append hprefix tailTrace_7413348
  have hstable : (prefixWord ++ tailWord_7413348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7413348).length < 2 ^ (prefixWord ++ tailWord_7413348).sum := by decide
  have hdescent : baseEnd_7413348 < baseStart_7413348 := by decide
  rcases family_descends (prefixWord ++ tailWord_7413348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7413361 : List Nat := [1, 2, 2, 2, 1, 1, 1, 2, 1, 6, 4]
def baseStart_7413361 : Nat := 118140960795 + 7413361 * 2 ^ 59
def prefixEnd_7413361 : Nat := 4983230072969 + 3 ^ 40 * 7413361 * 2
def baseEnd_7413361 : Nat := 3806617458295874924694079

theorem tailTrace_7413361 : CollatzResearch.WordTrace tailWord_7413361 prefixEnd_7413361 3806617458295874924694079 := by
  unfold tailWord_7413361
  simp only [CollatzResearch.WordTrace]
  refine ⟨270387488895666673104439937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180258325930444448736293291 270387488895666673104439937)
  ·
    refine ⟨202790616671750004828329953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 270387488895666673104439937 202790616671750004828329953)
    ·
      refine ⟨152092962503812503621247465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 202790616671750004828329953 152092962503812503621247465)
      ·
        refine ⟨114069721877859377715935599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 152092962503812503621247465 114069721877859377715935599)
        ·
          refine ⟨171104582816789066573903399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114069721877859377715935599 171104582816789066573903399)
          ·
            refine ⟨256656874225183599860855099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 171104582816789066573903399 256656874225183599860855099)
            ·
              refine ⟨384985311337775399791282649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 256656874225183599860855099 384985311337775399791282649)
              ·
                refine ⟨288738983503331549843461987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 384985311337775399791282649 288738983503331549843461987)
                ·
                  refine ⟨433108475254997324765192981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 288738983503331549843461987 433108475254997324765192981)
                  ·
                    refine ⟨20301959777577999598368421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 433108475254997324765192981 20301959777577999598368421)
                    ·
                      refine ⟨3806617458295874924694079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20301959777577999598368421 3806617458295874924694079)
                      ·
                        rfl

theorem cell23_7413361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 2, 1, 6, 4].length) (baseStart_7413361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7413361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7413361 prefixEnd_7413361 := by exact prefixLift 7413361
  have htrace : WordTrace (prefixWord ++ tailWord_7413361) baseStart_7413361 baseEnd_7413361 := by
    simpa [prefixWord, tailWord_7413361, baseEnd_7413361] using wordTrace_append hprefix tailTrace_7413361
  have hstable : (prefixWord ++ tailWord_7413361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7413361).length < 2 ^ (prefixWord ++ tailWord_7413361).sum := by decide
  have hdescent : baseEnd_7413361 < baseStart_7413361 := by decide
  rcases family_descends (prefixWord ++ tailWord_7413361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7413371 : List Nat := [1, 1, 1, 1, 1, 4, 5, 1, 8]
def baseStart_7413371 : Nat := 118140960795 + 7413371 * 2 ^ 59
def prefixEnd_7413371 : Nat := 4983230072969 + 3 ^ 40 * 7413371 * 2
def baseEnd_7413371 : Nat := 422958065900268876174337

theorem tailTrace_7413371 : CollatzResearch.WordTrace tailWord_7413371 prefixEnd_7413371 422958065900268876174337 := by
  unfold tailWord_7413371
  simp only [CollatzResearch.WordTrace]
  refine ⟨270387853625630444812303967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180258569083753629874869311 270387853625630444812303967)
  ·
    refine ⟨405581780438445667218455951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270387853625630444812303967 405581780438445667218455951)
    ·
      refine ⟨608372670657668500827683927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 405581780438445667218455951 608372670657668500827683927)
      ·
        refine ⟨912559005986502751241525891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 608372670657668500827683927 912559005986502751241525891)
        ·
          refine ⟨1368838508979754126862288837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 912559005986502751241525891 1368838508979754126862288837)
          ·
            refine ⟨256657220433703898786679157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1368838508979754126862288837 256657220433703898786679157)
            ·
              refine ⟨24061614415659740511251171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 256657220433703898786679157 24061614415659740511251171)
              ·
                refine ⟨36092421623489610766876757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24061614415659740511251171 36092421623489610766876757)
                ·
                  refine ⟨422958065900268876174337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 36092421623489610766876757 422958065900268876174337)
                  ·
                    rfl

theorem cell23_7413371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 5, 1, 8].length) (baseStart_7413371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7413371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7413371 prefixEnd_7413371 := by exact prefixLift 7413371
  have htrace : WordTrace (prefixWord ++ tailWord_7413371) baseStart_7413371 baseEnd_7413371 := by
    simpa [prefixWord, tailWord_7413371, baseEnd_7413371] using wordTrace_append hprefix tailTrace_7413371
  have hstable : (prefixWord ++ tailWord_7413371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7413371).length < 2 ^ (prefixWord ++ tailWord_7413371).sum := by decide
  have hdescent : baseEnd_7413371 < baseStart_7413371 := by decide
  rcases family_descends (prefixWord ++ tailWord_7413371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7413409 : List Nat := [1, 2, 3, 3, 2, 3, 1, 3, 1, 4]
def baseStart_7413409 : Nat := 118140960795 + 7413409 * 2 ^ 59
def prefixEnd_7413409 : Nat := 4983230072969 + 3 ^ 40 * 7413409 * 2
def baseEnd_7413409 : Nat := 1268880701789096912297953

theorem tailTrace_7413409 : CollatzResearch.WordTrace tailWord_7413409 prefixEnd_7413409 1268880701789096912297953 := by
  unfold tailWord_7413409
  simp only [CollatzResearch.WordTrace]
  refine ⟨270389239599492777302187281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180259493066328518201458187 270389239599492777302187281)
  ·
    refine ⟨202791929699619582976640461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 270389239599492777302187281 202791929699619582976640461)
    ·
      refine ⟨76046973637357343616240173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 202791929699619582976640461 76046973637357343616240173)
      ·
        refine ⟨28517615114009003856090065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76046973637357343616240173 28517615114009003856090065)
        ·
          refine ⟨21388211335506752892067549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28517615114009003856090065 21388211335506752892067549)
          ·
            refine ⟨8020579250815032334525331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21388211335506752892067549 8020579250815032334525331)
            ·
              refine ⟨12030868876222548501787997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8020579250815032334525331 12030868876222548501787997)
              ·
                refine ⟨4511575828583455688170499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12030868876222548501787997 4511575828583455688170499)
                ·
                  refine ⟨6767363742875183532255749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4511575828583455688170499 6767363742875183532255749)
                  ·
                    refine ⟨1268880701789096912297953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6767363742875183532255749 1268880701789096912297953)
                    ·
                      rfl

theorem cell23_7413409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 3, 1, 3, 1, 4].length) (baseStart_7413409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7413409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7413409 prefixEnd_7413409 := by exact prefixLift 7413409
  have htrace : WordTrace (prefixWord ++ tailWord_7413409) baseStart_7413409 baseEnd_7413409 := by
    simpa [prefixWord, tailWord_7413409, baseEnd_7413409] using wordTrace_append hprefix tailTrace_7413409
  have hstable : (prefixWord ++ tailWord_7413409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7413409).length < 2 ^ (prefixWord ++ tailWord_7413409).sum := by decide
  have hdescent : baseEnd_7413409 < baseStart_7413409 := by decide
  rcases family_descends (prefixWord ++ tailWord_7413409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7413432 : List Nat := [2, 1, 2, 1, 2, 1, 1, 8, 1, 1, 3]
def baseStart_7413432 : Nat := 118140960795 + 7413432 * 2 ^ 59
def prefixEnd_7413432 : Nat := 4983230072969 + 3 ^ 40 * 7413432 * 2
def baseEnd_7413432 : Nat := 3806653915422344146906253

theorem tailTrace_7413432 : CollatzResearch.WordTrace tailWord_7413432 prefixEnd_7413432 3806653915422344146906253 := by
  unfold tailWord_7413432
  simp only [CollatzResearch.WordTrace]
  refine ⟨135195039239204726115137275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180260052318939634820183033 135195039239204726115137275)
  ·
    refine ⟨202792558858807089172705913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135195039239204726115137275 202792558858807089172705913)
    ·
      refine ⟨152094419144105316879529435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 202792558858807089172705913 152094419144105316879529435)
      ·
        refine ⟨228141628716157975319294153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152094419144105316879529435 228141628716157975319294153)
        ·
          refine ⟨171106221537118481489470615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 228141628716157975319294153 171106221537118481489470615)
          ·
            refine ⟨256659332305677722234205923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 171106221537118481489470615 256659332305677722234205923)
            ·
              refine ⟨384988998458516583351308885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 256659332305677722234205923 384988998458516583351308885)
              ·
                refine ⟨4511589825685741211148151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 384988998458516583351308885 4511589825685741211148151)
                ·
                  refine ⟨6767384738528611816722227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4511589825685741211148151 6767384738528611816722227)
                  ·
                    refine ⟨10151077107792917725083341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6767384738528611816722227 10151077107792917725083341)
                    ·
                      refine ⟨3806653915422344146906253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10151077107792917725083341 3806653915422344146906253)
                      ·
                        rfl

theorem cell23_7413432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 8, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 8, 1, 1, 3].length) (baseStart_7413432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7413432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7413432 prefixEnd_7413432 := by exact prefixLift 7413432
  have htrace : WordTrace (prefixWord ++ tailWord_7413432) baseStart_7413432 baseEnd_7413432 := by
    simpa [prefixWord, tailWord_7413432, baseEnd_7413432] using wordTrace_append hprefix tailTrace_7413432
  have hstable : (prefixWord ++ tailWord_7413432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7413432).length < 2 ^ (prefixWord ++ tailWord_7413432).sum := by decide
  have hdescent : baseEnd_7413432 < baseStart_7413432 := by decide
  rcases family_descends (prefixWord ++ tailWord_7413432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7413448 : List Nat := [2, 1, 3, 1, 2, 2, 2, 3, 1, 6]
def baseStart_7413448 : Nat := 118140960795 + 7413448 * 2 ^ 59
def prefixEnd_7413448 : Nat := 4983230072969 + 3 ^ 40 * 7413448 * 2
def baseEnd_7413448 : Nat := 1268887377037605361435393

theorem tailTrace_7413448 : CollatzResearch.WordTrace tailWord_7413448 prefixEnd_7413448 1268887377037605361435393 := by
  unfold tailWord_7413448
  simp only [CollatzResearch.WordTrace]
  refine ⟨135195331023175743481428499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180260441364234324641904665 135195331023175743481428499)
  ·
    refine ⟨202792996534763615222142749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135195331023175743481428499 202792996534763615222142749)
    ·
      refine ⟨76047373700536355708303531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 202792996534763615222142749 76047373700536355708303531)
      ·
        refine ⟨114071060550804533562455297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76047373700536355708303531 114071060550804533562455297)
        ·
          refine ⟨85553295413103400171841473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114071060550804533562455297 85553295413103400171841473)
          ·
            refine ⟨64164971559827550128881105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85553295413103400171841473 64164971559827550128881105)
            ·
              refine ⟨48123728669870662596660829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64164971559827550128881105 48123728669870662596660829)
              ·
                refine ⟨18046398251201498473747811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48123728669870662596660829 18046398251201498473747811)
                ·
                  refine ⟨27069597376802247710621717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18046398251201498473747811 27069597376802247710621717)
                  ·
                    refine ⟨1268887377037605361435393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27069597376802247710621717 1268887377037605361435393)
                    ·
                      rfl

theorem cell23_7413448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 2, 3, 1, 6].length) (baseStart_7413448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7413448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7413448 prefixEnd_7413448 := by exact prefixLift 7413448
  have htrace : WordTrace (prefixWord ++ tailWord_7413448) baseStart_7413448 baseEnd_7413448 := by
    simpa [prefixWord, tailWord_7413448, baseEnd_7413448] using wordTrace_append hprefix tailTrace_7413448
  have hstable : (prefixWord ++ tailWord_7413448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7413448).length < 2 ^ (prefixWord ++ tailWord_7413448).sum := by decide
  have hdescent : baseEnd_7413448 < baseStart_7413448 := by decide
  rcases family_descends (prefixWord ++ tailWord_7413448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7413505 : List Nat := [1, 2, 4, 1, 1, 1, 3, 3, 1, 3, 3]
def baseStart_7413505 : Nat := 118140960795 + 7413505 * 2 ^ 59
def prefixEnd_7413505 : Nat := 4983230072969 + 3 ^ 40 * 7413505 * 2
def baseEnd_7413505 : Nat := 3806691399510122361293417

theorem tailTrace_7413505 : CollatzResearch.WordTrace tailWord_7413505 prefixEnd_7413505 3806691399510122361293417 := by
  unfold tailWord_7413505
  simp only [CollatzResearch.WordTrace]
  refine ⟨270392741007144985697681969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180261827338096657131787979 270392741007144985697681969)
  ·
    refine ⟨202794555755358739273261477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 270392741007144985697681969 202794555755358739273261477)
    ·
      refine ⟨38023979204129763613736527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 202794555755358739273261477 38023979204129763613736527)
      ·
        refine ⟨57035968806194645420604791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38023979204129763613736527 57035968806194645420604791)
        ·
          refine ⟨85553953209291968130907187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57035968806194645420604791 85553953209291968130907187)
          ·
            refine ⟨128330929813937952196360781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85553953209291968130907187 128330929813937952196360781)
            ·
              refine ⟨48124098680226732073635293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 128330929813937952196360781 48124098680226732073635293)
              ·
                refine ⟨18046537005085024527613235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48124098680226732073635293 18046537005085024527613235)
                ·
                  refine ⟨27069805507627536791419853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18046537005085024527613235 27069805507627536791419853)
                  ·
                    refine ⟨10151177065360326296782445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27069805507627536791419853 10151177065360326296782445)
                    ·
                      refine ⟨3806691399510122361293417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10151177065360326296782445 3806691399510122361293417)
                      ·
                        rfl

theorem cell23_7413505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 3, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 3, 3, 1, 3, 3].length) (baseStart_7413505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7413505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7413505 prefixEnd_7413505 := by exact prefixLift 7413505
  have htrace : WordTrace (prefixWord ++ tailWord_7413505) baseStart_7413505 baseEnd_7413505 := by
    simpa [prefixWord, tailWord_7413505, baseEnd_7413505] using wordTrace_append hprefix tailTrace_7413505
  have hstable : (prefixWord ++ tailWord_7413505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7413505).length < 2 ^ (prefixWord ++ tailWord_7413505).sum := by decide
  have hdescent : baseEnd_7413505 < baseStart_7413505 := by decide
  rcases family_descends (prefixWord ++ tailWord_7413505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7413510 : List Nat := [6, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2]
def baseStart_7413510 : Nat := 118140960795 + 7413510 * 2 ^ 59
def prefixEnd_7413510 : Nat := 4983230072969 + 3 ^ 40 * 7413510 * 2
def baseEnd_7413510 : Nat := 3806693966913394841730895

theorem tailTrace_7413510 : CollatzResearch.WordTrace tailWord_7413510 prefixEnd_7413510 3806693966913394841730895 := by
  unfold tailWord_7413510
  simp only [CollatzResearch.WordTrace]
  refine ⟨8449778855378964735987937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 180261948914751247701075989 8449778855378964735987937)
  ·
    refine ⟨6337334141534223551990953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8449778855378964735987937 6337334141534223551990953)
    ·
      refine ⟨4753000606150667663993215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6337334141534223551990953 4753000606150667663993215)
      ·
        refine ⟨7129500909226001495989823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4753000606150667663993215 7129500909226001495989823)
        ·
          refine ⟨10694251363839002243984735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7129500909226001495989823 10694251363839002243984735)
          ·
            refine ⟨16041377045758503365977103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10694251363839002243984735 16041377045758503365977103)
            ·
              refine ⟨24062065568637755048965655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16041377045758503365977103 24062065568637755048965655)
              ·
                refine ⟨36093098352956632573448483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24062065568637755048965655 36093098352956632573448483)
                ·
                  refine ⟨54139647529434948860172725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36093098352956632573448483 54139647529434948860172725)
                  ·
                    refine ⟨5075591955884526455641193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 54139647529434948860172725 5075591955884526455641193)
                    ·
                      refine ⟨3806693966913394841730895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5075591955884526455641193 3806693966913394841730895)
                      ·
                        rfl

theorem cell23_7413510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2].length) (baseStart_7413510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7413510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7413510 prefixEnd_7413510 := by exact prefixLift 7413510
  have htrace : WordTrace (prefixWord ++ tailWord_7413510) baseStart_7413510 baseEnd_7413510 := by
    simpa [prefixWord, tailWord_7413510, baseEnd_7413510] using wordTrace_append hprefix tailTrace_7413510
  have hstable : (prefixWord ++ tailWord_7413510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7413510).length < 2 ^ (prefixWord ++ tailWord_7413510).sum := by decide
  have hdescent : baseEnd_7413510 < baseStart_7413510 := by decide
  rcases family_descends (prefixWord ++ tailWord_7413510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7413517 : List Nat := [1, 7, 2, 1, 1, 1, 2, 3, 1, 1, 3]
def baseStart_7413517 : Nat := 118140960795 + 7413517 * 2 ^ 59
def prefixEnd_7413517 : Nat := 4983230072969 + 3 ^ 40 * 7413517 * 2
def baseEnd_7413517 : Nat := 3806697561277976314343363

theorem tailTrace_7413517 : CollatzResearch.WordTrace tailWord_7413517 prefixEnd_7413517 3806697561277976314343363 := by
  unfold tailWord_7413517
  simp only [CollatzResearch.WordTrace]
  refine ⟨270393178683101511747118805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180262119122067674498079203 270393178683101511747118805)
  ·
    refine ⟨6337340125385191681573097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 270393178683101511747118805 6337340125385191681573097)
    ·
      refine ⟨4753005094038893761179823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6337340125385191681573097 4753005094038893761179823)
      ·
        refine ⟨7129507641058340641769735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4753005094038893761179823 7129507641058340641769735)
        ·
          refine ⟨10694261461587510962654603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7129507641058340641769735 10694261461587510962654603)
          ·
            refine ⟨16041392192381266443981905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10694261461587510962654603 16041392192381266443981905)
            ·
              refine ⟨12031044144285949832986429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16041392192381266443981905 12031044144285949832986429)
              ·
                refine ⟨4511641554107231187369911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12031044144285949832986429 4511641554107231187369911)
                ·
                  refine ⟨6767462331160846781054867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4511641554107231187369911 6767462331160846781054867)
                  ·
                    refine ⟨10151193496741270171582301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6767462331160846781054867 10151193496741270171582301)
                    ·
                      refine ⟨3806697561277976314343363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10151193496741270171582301 3806697561277976314343363)
                      ·
                        rfl

theorem cell23_7413517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 2, 3, 1, 1, 3].length) (baseStart_7413517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7413517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7413517 prefixEnd_7413517 := by exact prefixLift 7413517
  have htrace : WordTrace (prefixWord ++ tailWord_7413517) baseStart_7413517 baseEnd_7413517 := by
    simpa [prefixWord, tailWord_7413517, baseEnd_7413517] using wordTrace_append hprefix tailTrace_7413517
  have hstable : (prefixWord ++ tailWord_7413517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7413517).length < 2 ^ (prefixWord ++ tailWord_7413517).sum := by decide
  have hdescent : baseEnd_7413517 < baseStart_7413517 := by decide
  rcases family_descends (prefixWord ++ tailWord_7413517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7413566 : List Nat := [4, 2, 1, 2, 2, 2, 2, 2, 1, 3, 2]
def baseStart_7413566 : Nat := 118140960795 + 7413566 * 2 ^ 59
def prefixEnd_7413566 : Nat := 4983230072969 + 3 ^ 40 * 7413566 * 2
def baseEnd_7413566 : Nat := 3806722721830046622630637

theorem tailTrace_7413566 : CollatzResearch.WordTrace tailWord_7413566 prefixEnd_7413566 3806722721830046622630637 := by
  unfold tailWord_7413566
  simp only [CollatzResearch.WordTrace]
  refine ⟨33799370732490499139456569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 180263310573282662077101701 33799370732490499139456569)
  ·
    refine ⟨25349528049367874354592427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33799370732490499139456569 25349528049367874354592427)
    ·
      refine ⟨38024292074051811531888641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25349528049367874354592427 38024292074051811531888641)
      ·
        refine ⟨28518219055538858648916481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38024292074051811531888641 28518219055538858648916481)
        ·
          refine ⟨21388664291654143986687361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28518219055538858648916481 21388664291654143986687361)
          ·
            refine ⟨16041498218740607990015521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21388664291654143986687361 16041498218740607990015521)
            ·
              refine ⟨12031123664055455992511641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16041498218740607990015521 12031123664055455992511641)
              ·
                refine ⟨9023342748041591994383731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12031123664055455992511641 9023342748041591994383731)
                ·
                  refine ⟨13535014122062387991575597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9023342748041591994383731 13535014122062387991575597)
                  ·
                    refine ⟨5075630295773395496840849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13535014122062387991575597 5075630295773395496840849)
                    ·
                      refine ⟨3806722721830046622630637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5075630295773395496840849 3806722721830046622630637)
                      ·
                        rfl

theorem cell23_7413566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 2, 2, 1, 3, 2].length) (baseStart_7413566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7413566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7413566 prefixEnd_7413566 := by exact prefixLift 7413566
  have htrace : WordTrace (prefixWord ++ tailWord_7413566) baseStart_7413566 baseEnd_7413566 := by
    simpa [prefixWord, tailWord_7413566, baseEnd_7413566] using wordTrace_append hprefix tailTrace_7413566
  have hstable : (prefixWord ++ tailWord_7413566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7413566).length < 2 ^ (prefixWord ++ tailWord_7413566).sum := by decide
  have hdescent : baseEnd_7413566 < baseStart_7413566 := by decide
  rcases family_descends (prefixWord ++ tailWord_7413566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7413602 : List Nat := [3, 3, 2, 1, 2, 1, 3, 1, 7]
def baseStart_7413602 : Nat := 118140960795 + 7413602 * 2 ^ 59
def prefixEnd_7413602 : Nat := 4983230072969 + 3 ^ 40 * 7413602 * 2
def baseEnd_7413602 : Nat := 422971245237067609086719

theorem tailTrace_7413602 : CollatzResearch.WordTrace tailWord_7413602 prefixEnd_7413602 422971245237067609086719 := by
  unfold tailWord_7413602
  simp only [CollatzResearch.WordTrace]
  refine ⟨67599069721948392815990765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 180264185925195714175975373 67599069721948392815990765)
  ·
    refine ⟨25349651145730647305996537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67599069721948392815990765 25349651145730647305996537)
    ·
      refine ⟨19012238359297985479497403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25349651145730647305996537 19012238359297985479497403)
      ·
        refine ⟨28518357538946978219246105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19012238359297985479497403 28518357538946978219246105)
        ·
          refine ⟨21388768154210233664434579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28518357538946978219246105 21388768154210233664434579)
          ·
            refine ⟨32083152231315350496651869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21388768154210233664434579 32083152231315350496651869)
            ·
              refine ⟨12031182086743256436244451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32083152231315350496651869 12031182086743256436244451)
              ·
                refine ⟨18046773130114884654366677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12031182086743256436244451 18046773130114884654366677)
                ·
                  refine ⟨422971245237067609086719, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18046773130114884654366677 422971245237067609086719)
                  ·
                    rfl

theorem cell23_7413602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 3, 1, 7].length) (baseStart_7413602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7413602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7413602 prefixEnd_7413602 := by exact prefixLift 7413602
  have htrace : WordTrace (prefixWord ++ tailWord_7413602) baseStart_7413602 baseEnd_7413602 := by
    simpa [prefixWord, tailWord_7413602, baseEnd_7413602] using wordTrace_append hprefix tailTrace_7413602
  have hstable : (prefixWord ++ tailWord_7413602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7413602).length < 2 ^ (prefixWord ++ tailWord_7413602).sum := by decide
  have hdescent : baseEnd_7413602 < baseStart_7413602 := by decide
  rcases family_descends (prefixWord ++ tailWord_7413602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7413719 : List Nat := [1, 1, 3, 2, 1, 1, 6, 1, 3, 1, 3]
def baseStart_7413719 : Nat := 118140960795 + 7413719 * 2 ^ 59
def prefixEnd_7413719 : Nat := 4983230072969 + 3 ^ 40 * 7413719 * 2
def baseEnd_7413719 : Nat := 3806801284370184524017433

theorem tailTrace_7413719 : CollatzResearch.WordTrace tailWord_7413719 prefixEnd_7413719 3806801284370184524017433 := by
  unfold tailWord_7413719
  simp only [CollatzResearch.WordTrace]
  refine ⟨270400546228369700245972211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180267030818913133497314807 270400546228369700245972211)
  ·
    refine ⟨405600819342554550368958317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270400546228369700245972211 405600819342554550368958317)
    ·
      refine ⟨152100307253457956388359369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 405600819342554550368958317 152100307253457956388359369)
      ·
        refine ⟨114075230440093467291269527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 152100307253457956388359369 114075230440093467291269527)
        ·
          refine ⟨171112845660140200936904291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114075230440093467291269527 171112845660140200936904291)
          ·
            refine ⟨256669268490210301405356437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 171112845660140200936904291 256669268490210301405356437)
            ·
              refine ⟨12031371960478607878376083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 256669268490210301405356437 12031371960478607878376083)
              ·
                refine ⟨18047057940717911817564125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12031371960478607878376083 18047057940717911817564125)
                ·
                  refine ⟨6767646727769216931586547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18047057940717911817564125 6767646727769216931586547)
                  ·
                    refine ⟨10151470091653825397379821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6767646727769216931586547 10151470091653825397379821)
                    ·
                      refine ⟨3806801284370184524017433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10151470091653825397379821 3806801284370184524017433)
                      ·
                        rfl

theorem cell23_7413719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 6, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 6, 1, 3, 1, 3].length) (baseStart_7413719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7413719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7413719 prefixEnd_7413719 := by exact prefixLift 7413719
  have htrace : WordTrace (prefixWord ++ tailWord_7413719) baseStart_7413719 baseEnd_7413719 := by
    simpa [prefixWord, tailWord_7413719, baseEnd_7413719] using wordTrace_append hprefix tailTrace_7413719
  have hstable : (prefixWord ++ tailWord_7413719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7413719).length < 2 ^ (prefixWord ++ tailWord_7413719).sum := by decide
  have hdescent : baseEnd_7413719 < baseStart_7413719 := by decide
  rcases family_descends (prefixWord ++ tailWord_7413719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7413752 : List Nat := [2, 1, 2, 1, 1, 3, 3, 2, 4, 4]
def baseStart_7413752 : Nat := 118140960795 + 7413752 * 2 ^ 59
def prefixEnd_7413752 : Nat := 4983230072969 + 3 ^ 40 * 7413752 * 2
def baseEnd_7413752 : Nat := 1268939409743927631634927

theorem tailTrace_7413752 : CollatzResearch.WordTrace tailWord_7413752 prefixEnd_7413752 1268939409743927631634927 := by
  unfold tailWord_7413752
  simp only [CollatzResearch.WordTrace]
  refine ⟨135200874918625073440961755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180267833224833431254615673 135200874918625073440961755)
  ·
    refine ⟨202801312377937610161442633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135200874918625073440961755 202801312377937610161442633)
    ·
      refine ⟨152100984283453207621081975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 202801312377937610161442633 152100984283453207621081975)
      ·
        refine ⟨228151476425179811431622963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152100984283453207621081975 228151476425179811431622963)
        ·
          refine ⟨342227214637769717147434445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 228151476425179811431622963 342227214637769717147434445)
          ·
            refine ⟨128335205489163643930287917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 342227214637769717147434445 128335205489163643930287917)
            ·
              refine ⟨48125702058436366473857969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 128335205489163643930287917 48125702058436366473857969)
              ·
                refine ⟨36094276543827274855393477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48125702058436366473857969 36094276543827274855393477)
                ·
                  refine ⟨6767676851967614035386277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36094276543827274855393477 6767676851967614035386277)
                  ·
                    refine ⟨1268939409743927631634927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6767676851967614035386277 1268939409743927631634927)
                    ·
                      rfl

theorem cell23_7413752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 3, 2, 4, 4].length) (baseStart_7413752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7413752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7413752 prefixEnd_7413752 := by exact prefixLift 7413752
  have htrace : WordTrace (prefixWord ++ tailWord_7413752) baseStart_7413752 baseEnd_7413752 := by
    simpa [prefixWord, tailWord_7413752, baseEnd_7413752] using wordTrace_append hprefix tailTrace_7413752
  have hstable : (prefixWord ++ tailWord_7413752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7413752).length < 2 ^ (prefixWord ++ tailWord_7413752).sum := by decide
  have hdescent : baseEnd_7413752 < baseStart_7413752 := by decide
  rcases family_descends (prefixWord ++ tailWord_7413752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7413753 : List Nat := [1, 2, 1, 3, 1, 6, 1, 3, 1, 1, 3]
def baseStart_7413753 : Nat := 118140960795 + 7413753 * 2 ^ 59
def prefixEnd_7413753 : Nat := 4983230072969 + 3 ^ 40 * 7413753 * 2
def baseEnd_7413753 : Nat := 3806818742712437390992277

theorem tailTrace_7413753 : CollatzResearch.WordTrace tailWord_7413753 prefixEnd_7413753 3806818742712437390992277 := by
  unfold tailWord_7413753
  simp only [CollatzResearch.WordTrace]
  refine ⟨270401786310246524052709913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180267857540164349368473275 270401786310246524052709913)
  ·
    refine ⟨202801339732684893039532435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 270401786310246524052709913 202801339732684893039532435)
    ·
      refine ⟨304202009599027339559298653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202801339732684893039532435 304202009599027339559298653)
      ·
        refine ⟨114075753599635252334736995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 304202009599027339559298653 114075753599635252334736995)
        ·
          refine ⟨171113630399452878502105493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114075753599635252334736995 171113630399452878502105493)
          ·
            refine ⟨8020951424974353679786195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 171113630399452878502105493 8020951424974353679786195)
            ·
              refine ⟨12031427137461530519679293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8020951424974353679786195 12031427137461530519679293)
              ·
                refine ⟨4511785176548073944879735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12031427137461530519679293 4511785176548073944879735)
                ·
                  refine ⟨6767677764822110917319603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4511785176548073944879735 6767677764822110917319603)
                  ·
                    refine ⟨10151516647233166375979405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6767677764822110917319603 10151516647233166375979405)
                    ·
                      refine ⟨3806818742712437390992277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10151516647233166375979405 3806818742712437390992277)
                      ·
                        rfl

theorem cell23_7413753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 6, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 6, 1, 3, 1, 1, 3].length) (baseStart_7413753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7413753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7413753 prefixEnd_7413753 := by exact prefixLift 7413753
  have htrace : WordTrace (prefixWord ++ tailWord_7413753) baseStart_7413753 baseEnd_7413753 := by
    simpa [prefixWord, tailWord_7413753, baseEnd_7413753] using wordTrace_append hprefix tailTrace_7413753
  have hstable : (prefixWord ++ tailWord_7413753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7413753).length < 2 ^ (prefixWord ++ tailWord_7413753).sum := by decide
  have hdescent : baseEnd_7413753 < baseStart_7413753 := by decide
  rcases family_descends (prefixWord ++ tailWord_7413753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7413759 : List Nat := [1, 1, 2, 2, 1, 2, 1, 4, 5, 2, 2]
def baseStart_7413759 : Nat := 118140960795 + 7413759 * 2 ^ 59
def prefixEnd_7413759 : Nat := 4983230072969 + 3 ^ 40 * 7413759 * 2
def baseEnd_7413759 : Nat := 3806821823596364367517249

theorem tailTrace_7413759 : CollatzResearch.WordTrace tailWord_7413759 prefixEnd_7413759 3806821823596364367517249 := by
  unfold tailWord_7413759
  simp only [CollatzResearch.WordTrace]
  refine ⟨270402005148224787077428331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180268003432149858051618887 270402005148224787077428331)
  ·
    refine ⟨405603007722337180616142497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270402005148224787077428331 405603007722337180616142497)
    ·
      refine ⟨304202255791752885462106873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 405603007722337180616142497 304202255791752885462106873)
      ·
        refine ⟨228151691843814664096580155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 304202255791752885462106873 228151691843814664096580155)
        ·
          refine ⟨342227537765721996144870233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 228151691843814664096580155 342227537765721996144870233)
          ·
            refine ⟨256670653324291497108652675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 342227537765721996144870233 256670653324291497108652675)
            ·
              refine ⟨385005979986437245662979013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 256670653324291497108652675 385005979986437245662979013)
              ·
                refine ⟨72188621247456983561808565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 385005979986437245662979013 72188621247456983561808565)
                ·
                  refine ⟨6767683241949092208919553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 72188621247456983561808565 6767683241949092208919553)
                  ·
                    refine ⟨5075762431461819156689665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6767683241949092208919553 5075762431461819156689665)
                    ·
                      refine ⟨3806821823596364367517249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5075762431461819156689665 3806821823596364367517249)
                      ·
                        rfl

theorem cell23_7413759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 4, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 4, 5, 2, 2].length) (baseStart_7413759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7413759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7413759 prefixEnd_7413759 := by exact prefixLift 7413759
  have htrace : WordTrace (prefixWord ++ tailWord_7413759) baseStart_7413759 baseEnd_7413759 := by
    simpa [prefixWord, tailWord_7413759, baseEnd_7413759] using wordTrace_append hprefix tailTrace_7413759
  have hstable : (prefixWord ++ tailWord_7413759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7413759).length < 2 ^ (prefixWord ++ tailWord_7413759).sum := by decide
  have hdescent : baseEnd_7413759 < baseStart_7413759 := by decide
  rcases family_descends (prefixWord ++ tailWord_7413759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7413765 : List Nat := [1, 3, 1, 1, 2, 4, 11]
def baseStart_7413765 : Nat := 118140960795 + 7413765 * 2 ^ 59
def prefixEnd_7413765 : Nat := 4983230072969 + 3 ^ 40 * 7413765 * 2
def baseEnd_7413765 : Nat := 46997838326917177086941

theorem tailTrace_7413765 : CollatzResearch.WordTrace tailWord_7413765 prefixEnd_7413765 46997838326917177086941 := by
  unfold tailWord_7413765
  simp only [CollatzResearch.WordTrace]
  refine ⟨270402223986203050102146749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180268149324135366734764499 270402223986203050102146749)
  ·
    refine ⟨101400833994826143788305031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 270402223986203050102146749 101400833994826143788305031)
    ·
      refine ⟨152101250992239215682457547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101400833994826143788305031 152101250992239215682457547)
      ·
        refine ⟨228151876488358823523686321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152101250992239215682457547 228151876488358823523686321)
        ·
          refine ⟨171113907366269117642764741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 228151876488358823523686321 171113907366269117642764741)
          ·
            refine ⟨32083857631175459558018389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 171113907366269117642764741 32083857631175459558018389)
            ·
              refine ⟨46997838326917177086941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 32083857631175459558018389 46997838326917177086941)
              ·
                rfl

theorem cell23_7413765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 11].length) (baseStart_7413765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7413765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7413765 prefixEnd_7413765 := by exact prefixLift 7413765
  have htrace : WordTrace (prefixWord ++ tailWord_7413765) baseStart_7413765 baseEnd_7413765 := by
    simpa [prefixWord, tailWord_7413765, baseEnd_7413765] using wordTrace_append hprefix tailTrace_7413765
  have hstable : (prefixWord ++ tailWord_7413765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7413765).length < 2 ^ (prefixWord ++ tailWord_7413765).sum := by decide
  have hdescent : baseEnd_7413765 < baseStart_7413765 := by decide
  rcases family_descends (prefixWord ++ tailWord_7413765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7413770 : List Nat := [3, 1, 2, 2, 4, 1, 3, 2, 1, 1, 3]
def baseStart_7413770 : Nat := 118140960795 + 7413770 * 2 ^ 59
def prefixEnd_7413770 : Nat := 4983230072969 + 3 ^ 40 * 7413770 * 2
def baseEnd_7413770 : Nat := 3806827471883563824479699

theorem tailTrace_7413770 : CollatzResearch.WordTrace tailWord_7413770 prefixEnd_7413770 3806827471883563824479699 := by
  unfold tailWord_7413770
  simp only [CollatzResearch.WordTrace]
  refine ⟨67600601587796233989019691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 180268270900789957304052509 67600601587796233989019691)
  ·
    refine ⟨101400902381694350983529537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67600601587796233989019691 101400902381694350983529537)
    ·
      refine ⟨76050676786270763237647153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101400902381694350983529537 76050676786270763237647153)
      ·
        refine ⟨57038007589703072428235365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76050676786270763237647153 57038007589703072428235365)
        ·
          refine ⟨10694626423069326080294131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 57038007589703072428235365 10694626423069326080294131)
          ·
            refine ⟨16041939634603989120441197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10694626423069326080294131 16041939634603989120441197)
            ·
              refine ⟨6015727362976495920165449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16041939634603989120441197 6015727362976495920165449)
              ·
                refine ⟨4511795522232371940124087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6015727362976495920165449 4511795522232371940124087)
                ·
                  refine ⟨6767693283348557910186131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4511795522232371940124087 6767693283348557910186131)
                  ·
                    refine ⟨10151539925022836865279197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6767693283348557910186131 10151539925022836865279197)
                    ·
                      refine ⟨3806827471883563824479699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10151539925022836865279197 3806827471883563824479699)
                      ·
                        rfl

theorem cell23_7413770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 3, 2, 1, 1, 3].length) (baseStart_7413770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7413770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7413770 prefixEnd_7413770 := by exact prefixLift 7413770
  have htrace : WordTrace (prefixWord ++ tailWord_7413770) baseStart_7413770 baseEnd_7413770 := by
    simpa [prefixWord, tailWord_7413770, baseEnd_7413770] using wordTrace_append hprefix tailTrace_7413770
  have hstable : (prefixWord ++ tailWord_7413770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7413770).length < 2 ^ (prefixWord ++ tailWord_7413770).sum := by decide
  have hdescent : baseEnd_7413770 < baseStart_7413770 := by decide
  rcases family_descends (prefixWord ++ tailWord_7413770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7413785 : List Nat := [1, 2, 1, 2, 1, 1, 3, 1, 1, 4, 6]
def baseStart_7413785 : Nat := 118140960795 + 7413785 * 2 ^ 59
def prefixEnd_7413785 : Nat := 4983230072969 + 3 ^ 40 * 7413785 * 2
def baseEnd_7413785 : Nat := 3806835174093381265792129

theorem tailTrace_7413785 : CollatzResearch.WordTrace tailWord_7413785 prefixEnd_7413785 3806835174093381265792129 := by
  unfold tailWord_7413785
  simp only [CollatzResearch.WordTrace]
  refine ⟨270402953446130593517874809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180268635630753729011916539 270402953446130593517874809)
  ·
    refine ⟨202802215084597945138406107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 270402953446130593517874809 202802215084597945138406107)
    ·
      refine ⟨304203322626896917707609161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202802215084597945138406107 304203322626896917707609161)
      ·
        refine ⟨228152491970172688280706871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 304203322626896917707609161 228152491970172688280706871)
        ·
          refine ⟨342228737955259032421060307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 228152491970172688280706871 342228737955259032421060307)
          ·
            refine ⟨513343106932888548631590461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 342228737955259032421060307 513343106932888548631590461)
            ·
              refine ⟨192503665099833205736846423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 513343106932888548631590461 192503665099833205736846423)
              ·
                refine ⟨288755497649749808605269635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 192503665099833205736846423 288755497649749808605269635)
                ·
                  refine ⟨433133246474624712907904453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 288755497649749808605269635 433133246474624712907904453)
                  ·
                    refine ⟨81212483713992133670232085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 433133246474624712907904453 81212483713992133670232085)
                    ·
                      refine ⟨3806835174093381265792129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 81212483713992133670232085 3806835174093381265792129)
                      ·
                        rfl

theorem cell23_7413785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 1, 1, 4, 6].length) (baseStart_7413785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7413785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7413785 prefixEnd_7413785 := by exact prefixLift 7413785
  have htrace : WordTrace (prefixWord ++ tailWord_7413785) baseStart_7413785 baseEnd_7413785 := by
    simpa [prefixWord, tailWord_7413785, baseEnd_7413785] using wordTrace_append hprefix tailTrace_7413785
  have hstable : (prefixWord ++ tailWord_7413785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7413785).length < 2 ^ (prefixWord ++ tailWord_7413785).sum := by decide
  have hdescent : baseEnd_7413785 < baseStart_7413785 := by decide
  rcases family_descends (prefixWord ++ tailWord_7413785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7413786 : List Nat := [3, 1, 1, 3, 1, 3, 4, 1, 2, 4]
def baseStart_7413786 : Nat := 118140960795 + 7413786 * 2 ^ 59
def prefixEnd_7413786 : Nat := 4983230072969 + 3 ^ 40 * 7413786 * 2
def baseEnd_7413786 : Nat := 1268945229191345253959875

theorem tailTrace_7413786 : CollatzResearch.WordTrace tailWord_7413786 prefixEnd_7413786 1268945229191345253959875 := by
  unfold tailWord_7413786
  simp only [CollatzResearch.WordTrace]
  refine ⟨67600747479781742672165303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 180268659946084647125774141 67600747479781742672165303)
  ·
    refine ⟨101401121219672614008247955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67600747479781742672165303 101401121219672614008247955)
    ·
      refine ⟨152101681829508921012371933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101401121219672614008247955 152101681829508921012371933)
      ·
        refine ⟨57038130686065845379639475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 152101681829508921012371933 57038130686065845379639475)
        ·
          refine ⟨85557196029098768069459213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57038130686065845379639475 85557196029098768069459213)
          ·
            refine ⟨32083948510912038026047205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 85557196029098768069459213 32083948510912038026047205)
            ·
              refine ⟨6015740345796007129883851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32083948510912038026047205 6015740345796007129883851)
              ·
                refine ⟨9023610518694010694825777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6015740345796007129883851 9023610518694010694825777)
                ·
                  refine ⟨6767707889020508021119333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9023610518694010694825777 6767707889020508021119333)
                  ·
                    refine ⟨1268945229191345253959875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6767707889020508021119333 1268945229191345253959875)
                    ·
                      rfl

theorem cell23_7413786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 4, 1, 2, 4].length) (baseStart_7413786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7413786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7413786 prefixEnd_7413786 := by exact prefixLift 7413786
  have htrace : WordTrace (prefixWord ++ tailWord_7413786) baseStart_7413786 baseEnd_7413786 := by
    simpa [prefixWord, tailWord_7413786, baseEnd_7413786] using wordTrace_append hprefix tailTrace_7413786
  have hstable : (prefixWord ++ tailWord_7413786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7413786).length < 2 ^ (prefixWord ++ tailWord_7413786).sum := by decide
  have hdescent : baseEnd_7413786 < baseStart_7413786 := by decide
  rcases family_descends (prefixWord ++ tailWord_7413786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7413793 : List Nat := [1, 2, 3, 2, 5, 1, 1, 2, 1, 1, 4]
def baseStart_7413793 : Nat := 118140960795 + 7413793 * 2 ^ 59
def prefixEnd_7413793 : Nat := 4983230072969 + 3 ^ 40 * 7413793 * 2
def baseEnd_7413793 : Nat := 3806839281938617234492093

theorem tailTrace_7413793 : CollatzResearch.WordTrace tailWord_7413793 prefixEnd_7413793 3806839281938617234492093 := by
  unfold tailWord_7413793
  simp only [CollatzResearch.WordTrace]
  refine ⟨270403245230101610884166033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180268830153401073922777355 270403245230101610884166033)
  ·
    refine ⟨202802433922576208163124525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 270403245230101610884166033 202802433922576208163124525)
    ·
      refine ⟨76050912720966078061171697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 202802433922576208163124525 76050912720966078061171697)
      ·
        refine ⟨57038184540724558545878773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76050912720966078061171697 57038184540724558545878773)
        ·
          refine ⟨5347329800692927363676135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 57038184540724558545878773 5347329800692927363676135)
          ·
            refine ⟨8020994701039391045514203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5347329800692927363676135 8020994701039391045514203)
            ·
              refine ⟨12031492051559086568271305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8020994701039391045514203 12031492051559086568271305)
              ·
                refine ⟨9023619038669314926203479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12031492051559086568271305 9023619038669314926203479)
                ·
                  refine ⟨13535428558003972389305219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9023619038669314926203479 13535428558003972389305219)
                  ·
                    refine ⟨20303142837005958583957829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13535428558003972389305219 20303142837005958583957829)
                    ·
                      refine ⟨3806839281938617234492093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20303142837005958583957829 3806839281938617234492093)
                      ·
                        rfl

theorem cell23_7413793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 5, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 5, 1, 1, 2, 1, 1, 4].length) (baseStart_7413793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7413793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7413793 prefixEnd_7413793 := by exact prefixLift 7413793
  have htrace : WordTrace (prefixWord ++ tailWord_7413793) baseStart_7413793 baseEnd_7413793 := by
    simpa [prefixWord, tailWord_7413793, baseEnd_7413793] using wordTrace_append hprefix tailTrace_7413793
  have hstable : (prefixWord ++ tailWord_7413793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7413793).length < 2 ^ (prefixWord ++ tailWord_7413793).sum := by decide
  have hdescent : baseEnd_7413793 < baseStart_7413793 := by decide
  rcases family_descends (prefixWord ++ tailWord_7413793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7413796 : List Nat := [2, 3, 1, 4, 2, 1, 1, 1, 3, 2, 3]
def baseStart_7413796 : Nat := 118140960795 + 7413796 * 2 ^ 59
def prefixEnd_7413796 : Nat := 4983230072969 + 3 ^ 40 * 7413796 * 2
def baseEnd_7413796 : Nat := 3806840822380580722754579

theorem tailTrace_7413796 : CollatzResearch.WordTrace tailWord_7413796 prefixEnd_7413796 3806840822380580722754579 := by
  unfold tailWord_7413796
  simp only [CollatzResearch.WordTrace]
  refine ⟨135201677324545371198262621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180268903099393828264350161 135201677324545371198262621)
  ·
    refine ⟨50700628996704514199348483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 135201677324545371198262621 50700628996704514199348483)
    ·
      refine ⟨76050943495056771299022725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50700628996704514199348483 76050943495056771299022725)
      ·
        refine ⟨14259551905323144618566761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 76050943495056771299022725 14259551905323144618566761)
        ·
          refine ⟨10694663928992358463925071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14259551905323144618566761 10694663928992358463925071)
          ·
            refine ⟨16041995893488537695887607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10694663928992358463925071 16041995893488537695887607)
            ·
              refine ⟨24062993840232806543831411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16041995893488537695887607 24062993840232806543831411)
              ·
                refine ⟨36094490760349209815747117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24062993840232806543831411 36094490760349209815747117)
                ·
                  refine ⟨13535434035130953680905169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36094490760349209815747117 13535434035130953680905169)
                  ·
                    refine ⟨10151575526348215260678877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13535434035130953680905169 10151575526348215260678877)
                    ·
                      refine ⟨3806840822380580722754579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10151575526348215260678877 3806840822380580722754579)
                      ·
                        rfl

theorem cell23_7413796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 1, 1, 3, 2, 3].length) (baseStart_7413796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7413796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7413796 prefixEnd_7413796 := by exact prefixLift 7413796
  have htrace : WordTrace (prefixWord ++ tailWord_7413796) baseStart_7413796 baseEnd_7413796 := by
    simpa [prefixWord, tailWord_7413796, baseEnd_7413796] using wordTrace_append hprefix tailTrace_7413796
  have hstable : (prefixWord ++ tailWord_7413796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7413796).length < 2 ^ (prefixWord ++ tailWord_7413796).sum := by decide
  have hdescent : baseEnd_7413796 < baseStart_7413796 := by decide
  rcases family_descends (prefixWord ++ tailWord_7413796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7413809 : List Nat := [1, 2, 2, 3, 1, 4, 1, 2, 1, 3, 3]
def baseStart_7413809 : Nat := 118140960795 + 7413809 * 2 ^ 59
def prefixEnd_7413809 : Nat := 4983230072969 + 3 ^ 40 * 7413809 * 2
def baseEnd_7413809 : Nat := 3806847497629089171892019

theorem tailTrace_7413809 : CollatzResearch.WordTrace tailWord_7413809 prefixEnd_7413809 3806847497629089171892019 := by
  unfold tailWord_7413809
  simp only [CollatzResearch.WordTrace]
  refine ⟨270403828798043645616748481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180269219198695763744498987 270403828798043645616748481)
  ·
    refine ⟨202802871598532734212561361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 270403828798043645616748481 202802871598532734212561361)
    ·
      refine ⟨152102153698899550659421021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 202802871598532734212561361 152102153698899550659421021)
      ·
        refine ⟨57038307637087331497282883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 152102153698899550659421021 57038307637087331497282883)
        ·
          refine ⟨85557461455630997245924325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57038307637087331497282883 85557461455630997245924325)
          ·
            refine ⟨16042024022930811983610811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 85557461455630997245924325 16042024022930811983610811)
            ·
              refine ⟨24063036034396217975416217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16042024022930811983610811 24063036034396217975416217)
              ·
                refine ⟨18047277025797163481562163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24063036034396217975416217 18047277025797163481562163)
                ·
                  refine ⟨27070915538695745222343245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18047277025797163481562163 27070915538695745222343245)
                  ·
                    refine ⟨10151593327010904458378717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27070915538695745222343245 10151593327010904458378717)
                    ·
                      refine ⟨3806847497629089171892019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10151593327010904458378717 3806847497629089171892019)
                      ·
                        rfl

theorem cell23_7413809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 1, 2, 1, 3, 3].length) (baseStart_7413809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7413809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7413809 prefixEnd_7413809 := by exact prefixLift 7413809
  have htrace : WordTrace (prefixWord ++ tailWord_7413809) baseStart_7413809 baseEnd_7413809 := by
    simpa [prefixWord, tailWord_7413809, baseEnd_7413809] using wordTrace_append hprefix tailTrace_7413809
  have hstable : (prefixWord ++ tailWord_7413809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7413809).length < 2 ^ (prefixWord ++ tailWord_7413809).sum := by decide
  have hdescent : baseEnd_7413809 < baseStart_7413809 := by decide
  rcases family_descends (prefixWord ++ tailWord_7413809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7413853 : List Nat := [1, 4, 4, 1, 1, 1, 2, 1, 3, 3, 2]
def baseStart_7413853 : Nat := 118140960795 + 7413853 * 2 ^ 59
def prefixEnd_7413853 : Nat := 4983230072969 + 3 ^ 40 * 7413853 * 2
def baseEnd_7413853 : Nat := 3806870090777886999741817

theorem tailTrace_7413853 : CollatzResearch.WordTrace tailWord_7413853 prefixEnd_7413853 3806870090777886999741817 := by
  unfold tailWord_7413853
  simp only [CollatzResearch.WordTrace]
  refine ⟨270405433609884241131350213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180270289073256160754233475 270405433609884241131350213)
  ·
    refine ⟨50701018801853295212128165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 270405433609884241131350213 50701018801853295212128165)
    ·
      refine ⟨9506441025347492852274031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 50701018801853295212128165 9506441025347492852274031)
      ·
        refine ⟨14259661538021239278411047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9506441025347492852274031 14259661538021239278411047)
        ·
          refine ⟨21389492307031858917616571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14259661538021239278411047 21389492307031858917616571)
          ·
            refine ⟨32084238460547788376424857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21389492307031858917616571 32084238460547788376424857)
            ·
              refine ⟨24063178845410841282318643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32084238460547788376424857 24063178845410841282318643)
              ·
                refine ⟨36094768268116261923477965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24063178845410841282318643 36094768268116261923477965)
                ·
                  refine ⟨13535538100543598221304237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36094768268116261923477965 13535538100543598221304237)
                  ·
                    refine ⟨5075826787703849332989089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13535538100543598221304237 5075826787703849332989089)
                    ·
                      refine ⟨3806870090777886999741817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5075826787703849332989089 3806870090777886999741817)
                      ·
                        rfl

theorem cell23_7413853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 2, 1, 3, 3, 2].length) (baseStart_7413853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7413853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7413853 prefixEnd_7413853 := by exact prefixLift 7413853
  have htrace : WordTrace (prefixWord ++ tailWord_7413853) baseStart_7413853 baseEnd_7413853 := by
    simpa [prefixWord, tailWord_7413853, baseEnd_7413853] using wordTrace_append hprefix tailTrace_7413853
  have hstable : (prefixWord ++ tailWord_7413853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7413853).length < 2 ^ (prefixWord ++ tailWord_7413853).sum := by decide
  have hdescent : baseEnd_7413853 < baseStart_7413853 := by decide
  rcases family_descends (prefixWord ++ tailWord_7413853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7413919 : List Nat := [1, 1, 2, 6, 1, 1, 2, 1, 1, 7]
def baseStart_7413919 : Nat := 118140960795 + 7413919 * 2 ^ 59
def prefixEnd_7413919 : Nat := 4983230072969 + 3 ^ 40 * 7413919 * 2
def baseEnd_7413919 : Nat := 1268967993500361247172171

theorem tailTrace_7413919 : CollatzResearch.WordTrace tailWord_7413919 prefixEnd_7413919 1268967993500361247172171 := by
  unfold tailWord_7413919
  simp only [CollatzResearch.WordTrace]
  refine ⟨270407840827645134403252811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180271893885096756268835207 270407840827645134403252811)
  ·
    refine ⟨405611761241467701604879217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270407840827645134403252811 405611761241467701604879217)
    ·
      refine ⟨304208820931100776203659413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 405611761241467701604879217 304208820931100776203659413)
      ·
        refine ⟨14259788481145348884546535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 304208820931100776203659413 14259788481145348884546535)
        ·
          refine ⟨21389682721718023326819803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14259788481145348884546535 21389682721718023326819803)
          ·
            refine ⟨32084524082577034990229705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21389682721718023326819803 32084524082577034990229705)
            ·
              refine ⟨24063393061932776242672279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32084524082577034990229705 24063393061932776242672279)
              ·
                refine ⟨36095089592899164364008419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24063393061932776242672279 36095089592899164364008419)
                ·
                  refine ⟨54142634389348746546012629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36095089592899164364008419 54142634389348746546012629)
                  ·
                    refine ⟨1268967993500361247172171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 54142634389348746546012629 1268967993500361247172171)
                    ·
                      rfl

theorem cell23_7413919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 2, 1, 1, 7].length) (baseStart_7413919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7413919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7413919 prefixEnd_7413919 := by exact prefixLift 7413919
  have htrace : WordTrace (prefixWord ++ tailWord_7413919) baseStart_7413919 baseEnd_7413919 := by
    simpa [prefixWord, tailWord_7413919, baseEnd_7413919] using wordTrace_append hprefix tailTrace_7413919
  have hstable : (prefixWord ++ tailWord_7413919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7413919).length < 2 ^ (prefixWord ++ tailWord_7413919).sum := by decide
  have hdescent : baseEnd_7413919 < baseStart_7413919 := by decide
  rcases family_descends (prefixWord ++ tailWord_7413919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7413973 : List Nat := [1, 3, 2, 4, 2, 1, 2, 1, 2, 1, 4]
def baseStart_7413973 : Nat := 118140960795 + 7413973 * 2 ^ 59
def prefixEnd_7413973 : Nat := 4983230072969 + 3 ^ 40 * 7413973 * 2
def baseEnd_7413973 : Nat := 3806931708456426530241265

theorem tailTrace_7413973 : CollatzResearch.WordTrace tailWord_7413973 prefixEnd_7413973 3806931708456426530241265 := by
  unfold tailWord_7413973
  simp only [CollatzResearch.WordTrace]
  refine ⟨270409810369449501625718573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180273206912966334417145715 270409810369449501625718573)
  ·
    refine ⟨101403678888543563109644465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 270409810369449501625718573 101403678888543563109644465)
    ·
      refine ⟨76052759166407672332233349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101403678888543563109644465 76052759166407672332233349)
      ·
        refine ⟨14259892343701438562293753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 76052759166407672332233349 14259892343701438562293753)
        ·
          refine ⟨10694919257776078921720315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14259892343701438562293753 10694919257776078921720315)
          ·
            refine ⟨16042378886664118382580473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10694919257776078921720315 16042378886664118382580473)
            ·
              refine ⟨12031784164998088786935355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16042378886664118382580473 12031784164998088786935355)
              ·
                refine ⟨18047676247497133180403033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12031784164998088786935355 18047676247497133180403033)
                ·
                  refine ⟨13535757185622849885302275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18047676247497133180403033 13535757185622849885302275)
                  ·
                    refine ⟨20303635778434274827953413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13535757185622849885302275 20303635778434274827953413)
                    ·
                      refine ⟨3806931708456426530241265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20303635778434274827953413 3806931708456426530241265)
                      ·
                        rfl

theorem cell23_7413973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 2, 1, 2, 1, 4].length) (baseStart_7413973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7413973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7413973 prefixEnd_7413973 := by exact prefixLift 7413973
  have htrace : WordTrace (prefixWord ++ tailWord_7413973) baseStart_7413973 baseEnd_7413973 := by
    simpa [prefixWord, tailWord_7413973, baseEnd_7413973] using wordTrace_append hprefix tailTrace_7413973
  have hstable : (prefixWord ++ tailWord_7413973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7413973).length < 2 ^ (prefixWord ++ tailWord_7413973).sum := by decide
  have hdescent : baseEnd_7413973 < baseStart_7413973 := by decide
  rcases family_descends (prefixWord ++ tailWord_7413973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7413976 : List Nat := [2, 1, 2, 2, 4, 1, 1, 3, 2, 2, 3]
def baseStart_7413976 : Nat := 118140960795 + 7413976 * 2 ^ 59
def prefixEnd_7413976 : Nat := 4983230072969 + 3 ^ 40 * 7413976 * 2
def baseEnd_7413976 : Nat := 3806933248898390018503751

theorem tailTrace_7413976 : CollatzResearch.WordTrace tailWord_7413976 prefixEnd_7413976 3806933248898390018503751 := by
  unfold tailWord_7413976
  simp only [CollatzResearch.WordTrace]
  refine ⟨135204959894219316569038891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180273279858959088758718521 135204959894219316569038891)
  ·
    refine ⟨202807439841328974853558337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135204959894219316569038891 202807439841328974853558337)
    ·
      refine ⟨152105579880996731140168753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 202807439841328974853558337 152105579880996731140168753)
      ·
        refine ⟨114079184910747548355126565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 152105579880996731140168753 114079184910747548355126565)
        ·
          refine ⟨21389847170765165316586231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 114079184910747548355126565 21389847170765165316586231)
          ·
            refine ⟨32084770756147747974879347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21389847170765165316586231 32084770756147747974879347)
            ·
              refine ⟨48127156134221621962319021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32084770756147747974879347 48127156134221621962319021)
              ·
                refine ⟨18047683550333108235869633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48127156134221621962319021 18047683550333108235869633)
                ·
                  refine ⟨13535762662749831176902225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18047683550333108235869633 13535762662749831176902225)
                  ·
                    refine ⟨10151821997062373382676669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13535762662749831176902225 10151821997062373382676669)
                    ·
                      refine ⟨3806933248898390018503751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10151821997062373382676669 3806933248898390018503751)
                      ·
                        rfl

theorem cell23_7413976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 1, 3, 2, 2, 3].length) (baseStart_7413976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7413976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7413976 prefixEnd_7413976 := by exact prefixLift 7413976
  have htrace : WordTrace (prefixWord ++ tailWord_7413976) baseStart_7413976 baseEnd_7413976 := by
    simpa [prefixWord, tailWord_7413976, baseEnd_7413976] using wordTrace_append hprefix tailTrace_7413976
  have hstable : (prefixWord ++ tailWord_7413976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7413976).length < 2 ^ (prefixWord ++ tailWord_7413976).sum := by decide
  have hdescent : baseEnd_7413976 < baseStart_7413976 := by decide
  rcases family_descends (prefixWord ++ tailWord_7413976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7414016 : List Nat := [2, 1, 1, 2, 1, 1, 4, 2, 4, 3, 2]
def baseStart_7414016 : Nat := 118140960795 + 7414016 * 2 ^ 59
def prefixEnd_7414016 : Nat := 4983230072969 + 3 ^ 40 * 7414016 * 2
def baseEnd_7414016 : Nat := 3806953788124569862003567

theorem tailTrace_7414016 : CollatzResearch.WordTrace tailWord_7414016 prefixEnd_7414016 3806953788124569862003567 := by
  unfold tailWord_7414016
  simp only [CollatzResearch.WordTrace]
  refine ⟨135205689354146859984766951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180274252472195813313022601 135205689354146859984766951)
  ·
    refine ⟨202808534031220289977150427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135205689354146859984766951 202808534031220289977150427)
    ·
      refine ⟨304212801046830434965725641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202808534031220289977150427 304212801046830434965725641)
      ·
        refine ⟨228159600785122826224294231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 304212801046830434965725641 228159600785122826224294231)
        ·
          refine ⟨342239401177684239336441347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 228159600785122826224294231 342239401177684239336441347)
          ·
            refine ⟨513359101766526359004662021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 342239401177684239336441347 513359101766526359004662021)
            ·
              refine ⟨96254831581223692313374129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 513359101766526359004662021 96254831581223692313374129)
              ·
                refine ⟨72191123685917769235030597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 96254831581223692313374129 72191123685917769235030597)
                ·
                  refine ⟨13535835691109581731568237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 72191123685917769235030597 13535835691109581731568237)
                  ·
                    refine ⟨5075938384166093149338089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13535835691109581731568237 5075938384166093149338089)
                    ·
                      refine ⟨3806953788124569862003567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5075938384166093149338089 3806953788124569862003567)
                      ·
                        rfl

theorem cell23_7414016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 2, 4, 3, 2].length) (baseStart_7414016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7414016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7414016 prefixEnd_7414016 := by exact prefixLift 7414016
  have htrace : WordTrace (prefixWord ++ tailWord_7414016) baseStart_7414016 baseEnd_7414016 := by
    simpa [prefixWord, tailWord_7414016, baseEnd_7414016] using wordTrace_append hprefix tailTrace_7414016
  have hstable : (prefixWord ++ tailWord_7414016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7414016).length < 2 ^ (prefixWord ++ tailWord_7414016).sum := by decide
  have hdescent : baseEnd_7414016 < baseStart_7414016 := by decide
  rcases family_descends (prefixWord ++ tailWord_7414016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7414033 : List Nat := [1, 2, 2, 1, 1, 5, 3, 1, 2, 3, 2]
def baseStart_7414033 : Nat := 118140960795 + 7414033 * 2 ^ 59
def prefixEnd_7414033 : Nat := 4983230072969 + 3 ^ 40 * 7414033 * 2
def baseEnd_7414033 : Nat := 3806962517295696295490989

theorem tailTrace_7414033 : CollatzResearch.WordTrace tailWord_7414033 prefixEnd_7414033 3806962517295696295490989 := by
  unfold tailWord_7414033
  simp only [CollatzResearch.WordTrace]
  refine ⟨270411998749232131872902753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180274665832821421248601835 270411998749232131872902753)
  ·
    refine ⟨202808999061924098904677065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 270411998749232131872902753 202808999061924098904677065)
    ·
      refine ⟨152106749296443074178507799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 202808999061924098904677065 152106749296443074178507799)
      ·
        refine ⟨228160123944664611267761699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152106749296443074178507799 228160123944664611267761699)
        ·
          refine ⟨342240185916996916901642549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 228160123944664611267761699 342240185916996916901642549)
          ·
            refine ⟨32085017429718460959528989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 342240185916996916901642549 32085017429718460959528989)
            ·
              refine ⟨12031881536144422859823371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32085017429718460959528989 12031881536144422859823371)
              ·
                refine ⟨18047822304216634289735057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12031881536144422859823371 18047822304216634289735057)
                ·
                  refine ⟨13535866728162475717301293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18047822304216634289735057 13535866728162475717301293)
                  ·
                    refine ⟨5075950023060928393987985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13535866728162475717301293 5075950023060928393987985)
                    ·
                      refine ⟨3806962517295696295490989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5075950023060928393987985 3806962517295696295490989)
                      ·
                        rfl

theorem cell23_7414033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 3, 2].length) (baseStart_7414033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7414033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7414033 prefixEnd_7414033 := by exact prefixLift 7414033
  have htrace : WordTrace (prefixWord ++ tailWord_7414033) baseStart_7414033 baseEnd_7414033 := by
    simpa [prefixWord, tailWord_7414033, baseEnd_7414033] using wordTrace_append hprefix tailTrace_7414033
  have hstable : (prefixWord ++ tailWord_7414033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7414033).length < 2 ^ (prefixWord ++ tailWord_7414033).sum := by decide
  have hdescent : baseEnd_7414033 < baseStart_7414033 := by decide
  rcases family_descends (prefixWord ++ tailWord_7414033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7414040 : List Nat := [2, 1, 2, 3, 1, 2, 4, 3, 1, 1, 3]
def baseStart_7414040 : Nat := 118140960795 + 7414040 * 2 ^ 59
def prefixEnd_7414040 : Nat := 4983230072969 + 3 ^ 40 * 7414040 * 2
def baseEnd_7414040 : Nat := 3806966111660277768103457

theorem tailTrace_7414040 : CollatzResearch.WordTrace tailWord_7414040 prefixEnd_7414040 3806966111660277768103457 := by
  unfold tailWord_7414040
  simp only [CollatzResearch.WordTrace]
  refine ⟨135206127030103386034203787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180274836040137848045605049 135206127030103386034203787)
  ·
    refine ⟨202809190545155079051305681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135206127030103386034203787 202809190545155079051305681)
    ·
      refine ⟨152106892908866309288479261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 202809190545155079051305681 152106892908866309288479261)
      ·
        refine ⟨57040084840824865983179723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 152106892908866309288479261 57040084840824865983179723)
        ·
          refine ⟨85560127261237298974769585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57040084840824865983179723 85560127261237298974769585)
          ·
            refine ⟨64170095445927974231077189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85560127261237298974769585 64170095445927974231077189)
            ·
              refine ⟨12031892896111495168326973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 64170095445927974231077189 12031892896111495168326973)
              ·
                refine ⟨4511959836041810688122615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12031892896111495168326973 4511959836041810688122615)
                ·
                  refine ⟨6767939754062716032183923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4511959836041810688122615 6767939754062716032183923)
                  ·
                    refine ⟨10151909631094074048275885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6767939754062716032183923 10151909631094074048275885)
                    ·
                      refine ⟨3806966111660277768103457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10151909631094074048275885 3806966111660277768103457)
                      ·
                        rfl

theorem cell23_7414040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 4, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 4, 3, 1, 1, 3].length) (baseStart_7414040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7414040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7414040 prefixEnd_7414040 := by exact prefixLift 7414040
  have htrace : WordTrace (prefixWord ++ tailWord_7414040) baseStart_7414040 baseEnd_7414040 := by
    simpa [prefixWord, tailWord_7414040, baseEnd_7414040] using wordTrace_append hprefix tailTrace_7414040
  have hstable : (prefixWord ++ tailWord_7414040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7414040).length < 2 ^ (prefixWord ++ tailWord_7414040).sum := by decide
  have hdescent : baseEnd_7414040 < baseStart_7414040 := by decide
  rcases family_descends (prefixWord ++ tailWord_7414040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7414063 : List Nat := [1, 1, 2, 1, 2, 1, 5, 3, 3, 2, 2]
def baseStart_7414063 : Nat := 118140960795 + 7414063 * 2 ^ 59
def prefixEnd_7414063 : Nat := 4983230072969 + 3 ^ 40 * 7414063 * 2
def baseEnd_7414063 : Nat := 3806977921715331178115851

theorem tailTrace_7414063 : CollatzResearch.WordTrace tailWord_7414063 prefixEnd_7414063 3806977921715331178115851 := by
  unfold tailWord_7414063
  simp only [CollatzResearch.WordTrace]
  refine ⟨270413092939123446996494843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180275395292748964664329895 270413092939123446996494843)
  ·
    refine ⟨405619639408685170494742265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270413092939123446996494843 405619639408685170494742265)
    ·
      refine ⟨304214729556513877871056699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 405619639408685170494742265 304214729556513877871056699)
      ·
        refine ⟨456322094334770816806585049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 304214729556513877871056699 456322094334770816806585049)
        ·
          refine ⟨342241570751078112604938787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 456322094334770816806585049 342241570751078112604938787)
          ·
            refine ⟨513362356126617168907408181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 342241570751078112604938787 513362356126617168907408181)
            ·
              refine ⟨48127720886870359585069517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 513362356126617168907408181 48127720886870359585069517)
              ·
                refine ⟨18047895332576384844401069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48127720886870359585069517 18047895332576384844401069)
                ·
                  refine ⟨6767960749716144316650401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18047895332576384844401069 6767960749716144316650401)
                  ·
                    refine ⟨5075970562287108237487801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6767960749716144316650401 5075970562287108237487801)
                    ·
                      refine ⟨3806977921715331178115851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5075970562287108237487801 3806977921715331178115851)
                      ·
                        rfl

theorem cell23_7414063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 5, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 5, 3, 3, 2, 2].length) (baseStart_7414063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7414063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7414063 prefixEnd_7414063 := by exact prefixLift 7414063
  have htrace : WordTrace (prefixWord ++ tailWord_7414063) baseStart_7414063 baseEnd_7414063 := by
    simpa [prefixWord, tailWord_7414063, baseEnd_7414063] using wordTrace_append hprefix tailTrace_7414063
  have hstable : (prefixWord ++ tailWord_7414063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7414063).length < 2 ^ (prefixWord ++ tailWord_7414063).sum := by decide
  have hdescent : baseEnd_7414063 < baseStart_7414063 := by decide
  rcases family_descends (prefixWord ++ tailWord_7414063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7414069 : List Nat := [1, 3, 3, 1, 2, 1, 2, 10]
def baseStart_7414069 : Nat := 118140960795 + 7414069 * 2 ^ 59
def prefixEnd_7414069 : Nat := 4983230072969 + 3 ^ 40 * 7414069 * 2
def baseEnd_7414069 : Nat := 140999296392565116838549

theorem tailTrace_7414069 : CollatzResearch.WordTrace tailWord_7414069 prefixEnd_7414069 140999296392565116838549 := by
  unfold tailWord_7414069
  simp only [CollatzResearch.WordTrace]
  refine ⟨270413311777101710021213261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180275541184734473347475507 270413311777101710021213261)
  ·
    refine ⟨101404991916413141257954973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 270413311777101710021213261 101404991916413141257954973)
    ·
      refine ⟨38026871968654927971733115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 101404991916413141257954973 38026871968654927971733115)
      ·
        refine ⟨57040307952982391957599673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38026871968654927971733115 57040307952982391957599673)
        ·
          refine ⟨42780230964736793968199755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57040307952982391957599673 42780230964736793968199755)
          ·
            refine ⟨64170346447105190952299633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42780230964736793968199755 64170346447105190952299633)
            ·
              refine ⟨48127759835328893214224725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64170346447105190952299633 48127759835328893214224725)
              ·
                refine ⟨140999296392565116838549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 48127759835328893214224725 140999296392565116838549)
                ·
                  rfl

theorem cell23_7414069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 2, 10].length) (baseStart_7414069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7414069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7414069 prefixEnd_7414069 := by exact prefixLift 7414069
  have htrace : WordTrace (prefixWord ++ tailWord_7414069) baseStart_7414069 baseEnd_7414069 := by
    simpa [prefixWord, tailWord_7414069, baseEnd_7414069] using wordTrace_append hprefix tailTrace_7414069
  have hstable : (prefixWord ++ tailWord_7414069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7414069).length < 2 ^ (prefixWord ++ tailWord_7414069).sum := by decide
  have hdescent : baseEnd_7414069 < baseStart_7414069 := by decide
  rcases family_descends (prefixWord ++ tailWord_7414069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7414073 : List Nat := [1, 2, 1, 6, 1, 3, 1, 1, 1, 6]
def baseStart_7414073 : Nat := 118140960795 + 7414073 * 2 ^ 59
def prefixEnd_7414073 : Nat := 4983230072969 + 3 ^ 40 * 7414073 * 2
def baseEnd_7414073 : Nat := 1268994352173958712996935

theorem tailTrace_7414073 : CollatzResearch.WordTrace tailWord_7414073 prefixEnd_7414073 1268994352173958712996935 := by
  unfold tailWord_7414073
  simp only [CollatzResearch.WordTrace]
  refine ⟨270413457669087218704358873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180275638446058145802905915 270413457669087218704358873)
  ·
    refine ⟨202810093251815414028269155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 270413457669087218704358873 202810093251815414028269155)
    ·
      refine ⟨304215139877723121042403733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202810093251815414028269155 304215139877723121042403733)
      ·
        refine ⟨14260084681768271298862675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 304215139877723121042403733 14260084681768271298862675)
        ·
          refine ⟨21390127022652406948294013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14260084681768271298862675 21390127022652406948294013)
          ·
            refine ⟨8021297633494652605610255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21390127022652406948294013 8021297633494652605610255)
            ·
              refine ⟨12031946450241978908415383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8021297633494652605610255 12031946450241978908415383)
              ·
                refine ⟨18047919675362968362623075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12031946450241978908415383 18047919675362968362623075)
                ·
                  refine ⟨27071879513044452543934613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18047919675362968362623075 27071879513044452543934613)
                  ·
                    refine ⟨1268994352173958712996935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27071879513044452543934613 1268994352173958712996935)
                    ·
                      rfl

theorem cell23_7414073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 3, 1, 1, 1, 6].length) (baseStart_7414073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7414073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7414073 prefixEnd_7414073 := by exact prefixLift 7414073
  have htrace : WordTrace (prefixWord ++ tailWord_7414073) baseStart_7414073 baseEnd_7414073 := by
    simpa [prefixWord, tailWord_7414073, baseEnd_7414073] using wordTrace_append hprefix tailTrace_7414073
  have hstable : (prefixWord ++ tailWord_7414073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7414073).length < 2 ^ (prefixWord ++ tailWord_7414073).sum := by decide
  have hdescent : baseEnd_7414073 < baseStart_7414073 := by decide
  rcases family_descends (prefixWord ++ tailWord_7414073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7414097 : List Nat := [1, 2, 2, 1, 4, 2, 3, 3, 1, 2, 2]
def baseStart_7414097 : Nat := 118140960795 + 7414097 * 2 ^ 59
def prefixEnd_7414097 : Nat := 4983230072969 + 3 ^ 40 * 7414097 * 2
def baseEnd_7414097 : Nat := 3806995380057584045090695

theorem tailTrace_7414097 : CollatzResearch.WordTrace tailWord_7414097 prefixEnd_7414097 3806995380057584045090695 := by
  unfold tailWord_7414097
  simp only [CollatzResearch.WordTrace]
  refine ⟨270414333021000270803232545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180276222014000180535488363 270414333021000270803232545)
  ·
    refine ⟨202810749765750203102424409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 270414333021000270803232545 202810749765750203102424409)
    ·
      refine ⟨152108062324312652326818307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 202810749765750203102424409 152108062324312652326818307)
      ·
        refine ⟨228162093486468978490227461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152108062324312652326818307 228162093486468978490227461)
        ·
          refine ⟨42780392528712933466917649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 228162093486468978490227461 42780392528712933466917649)
          ·
            refine ⟨32085294396534700100188237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42780392528712933466917649 32085294396534700100188237)
            ·
              refine ⟨12031985398700512537570589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32085294396534700100188237 12031985398700512537570589)
              ·
                refine ⟨4511994524512692201588971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12031985398700512537570589 4511994524512692201588971)
                ·
                  refine ⟨6767991786769038302383457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4511994524512692201588971 6767991786769038302383457)
                  ·
                    refine ⟨5075993840076778726787593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6767991786769038302383457 5075993840076778726787593)
                    ·
                      refine ⟨3806995380057584045090695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5075993840076778726787593 3806995380057584045090695)
                      ·
                        rfl

theorem cell23_7414097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 3, 3, 1, 2, 2].length) (baseStart_7414097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7414097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7414097 prefixEnd_7414097 := by exact prefixLift 7414097
  have htrace : WordTrace (prefixWord ++ tailWord_7414097) baseStart_7414097 baseEnd_7414097 := by
    simpa [prefixWord, tailWord_7414097, baseEnd_7414097] using wordTrace_append hprefix tailTrace_7414097
  have hstable : (prefixWord ++ tailWord_7414097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7414097).length < 2 ^ (prefixWord ++ tailWord_7414097).sum := by decide
  have hdescent : baseEnd_7414097 < baseStart_7414097 := by decide
  rcases family_descends (prefixWord ++ tailWord_7414097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7414129 : List Nat := [1, 2, 2, 2, 1, 2, 1, 3, 1, 8]
def baseStart_7414129 : Nat := 118140960795 + 7414129 * 2 ^ 59
def prefixEnd_7414129 : Nat := 4983230072969 + 3 ^ 40 * 7414129 * 2
def baseEnd_7414129 : Nat := 1269003937146175973296849

theorem tailTrace_7414129 : CollatzResearch.WordTrace tailWord_7414129 prefixEnd_7414129 1269003937146175973296849 := by
  unfold tailWord_7414129
  simp only [CollatzResearch.WordTrace]
  refine ⟨270415500156884340268397441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180277000104589560178931627 270415500156884340268397441)
  ·
    refine ⟨202811625117663255201298081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 270415500156884340268397441 202811625117663255201298081)
    ·
      refine ⟨152108718838247441400973561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 202811625117663255201298081 152108718838247441400973561)
      ·
        refine ⟨114081539128685581050730171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 152108718838247441400973561 114081539128685581050730171)
        ·
          refine ⟨171122308693028371576095257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114081539128685581050730171 171122308693028371576095257)
          ·
            refine ⟨128341731519771278682071443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 171122308693028371576095257 128341731519771278682071443)
            ·
              refine ⟨192512597279656918023107165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 128341731519771278682071443 192512597279656918023107165)
              ·
                refine ⟨72192223979871344258665187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 192512597279656918023107165 72192223979871344258665187)
                ·
                  refine ⟨108288335969807016387997781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 72192223979871344258665187 108288335969807016387997781)
                  ·
                    refine ⟨1269003937146175973296849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 108288335969807016387997781 1269003937146175973296849)
                    ·
                      rfl

theorem cell23_7414129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 3, 1, 8].length) (baseStart_7414129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7414129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7414129 prefixEnd_7414129 := by exact prefixLift 7414129
  have htrace : WordTrace (prefixWord ++ tailWord_7414129) baseStart_7414129 baseEnd_7414129 := by
    simpa [prefixWord, tailWord_7414129, baseEnd_7414129] using wordTrace_append hprefix tailTrace_7414129
  have hstable : (prefixWord ++ tailWord_7414129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7414129).length < 2 ^ (prefixWord ++ tailWord_7414129).sum := by decide
  have hdescent : baseEnd_7414129 < baseStart_7414129 := by decide
  rcases family_descends (prefixWord ++ tailWord_7414129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7414130 : List Nat := [3, 2, 1, 2, 1, 4, 1, 3, 2, 1, 3]
def baseStart_7414130 : Nat := 118140960795 + 7414130 * 2 ^ 59
def prefixEnd_7414130 : Nat := 4983230072969 + 3 ^ 40 * 7414130 * 2
def baseEnd_7414130 : Nat := 3807012324919182415978043

theorem tailTrace_7414130 : CollatzResearch.WordTrace tailWord_7414130 prefixEnd_7414130 3807012324919182415978043 := by
  unfold tailWord_7414130
  simp only [CollatzResearch.WordTrace]
  refine ⟨67603884157470179359795961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 180277024419920478292789229 67603884157470179359795961)
  ·
    refine ⟨50702913118102634519846971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67603884157470179359795961 50702913118102634519846971)
    ·
      refine ⟨76054369677153951779770457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50702913118102634519846971 76054369677153951779770457)
      ·
        refine ⟨57040777257865463834827843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76054369677153951779770457 57040777257865463834827843)
        ·
          refine ⟨85561165886798195752241765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57040777257865463834827843 85561165886798195752241765)
          ·
            refine ⟨16042718603774661703545331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 85561165886798195752241765 16042718603774661703545331)
            ·
              refine ⟨24064077905661992555317997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16042718603774661703545331 24064077905661992555317997)
              ·
                refine ⟨9024029214623247208244249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24064077905661992555317997 9024029214623247208244249)
                ·
                  refine ⟨6768021910967435406183187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9024029214623247208244249 6768021910967435406183187)
                  ·
                    refine ⟨10152032866451153109274781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6768021910967435406183187 10152032866451153109274781)
                    ·
                      refine ⟨3807012324919182415978043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10152032866451153109274781 3807012324919182415978043)
                      ·
                        rfl

theorem cell23_7414130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 1, 3, 2, 1, 3].length) (baseStart_7414130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7414130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7414130 prefixEnd_7414130 := by exact prefixLift 7414130
  have htrace : WordTrace (prefixWord ++ tailWord_7414130) baseStart_7414130 baseEnd_7414130 := by
    simpa [prefixWord, tailWord_7414130, baseEnd_7414130] using wordTrace_append hprefix tailTrace_7414130
  have hstable : (prefixWord ++ tailWord_7414130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7414130).length < 2 ^ (prefixWord ++ tailWord_7414130).sum := by decide
  have hdescent : baseEnd_7414130 < baseStart_7414130 := by decide
  rcases family_descends (prefixWord ++ tailWord_7414130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7414134 : List Nat := [5, 1, 1, 4, 1, 2, 1, 2, 1, 2, 3]
def baseStart_7414134 : Nat := 118140960795 + 7414134 * 2 ^ 59
def prefixEnd_7414134 : Nat := 4983230072969 + 3 ^ 40 * 7414134 * 2
def baseEnd_7414134 : Nat := 3807014378841800400328025

theorem tailTrace_7414134 : CollatzResearch.WordTrace tailWord_7414134 prefixEnd_7414134 3807014378841800400328025 := by
  unfold tailWord_7414134
  simp only [CollatzResearch.WordTrace]
  refine ⟨16900980157616639132645591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 180277121681244150748219637 16900980157616639132645591)
  ·
    refine ⟨25351470236424958698968387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16900980157616639132645591 25351470236424958698968387)
    ·
      refine ⟨38027205354637438048452581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25351470236424958698968387 38027205354637438048452581)
      ·
        refine ⟨7130101003994519634084859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38027205354637438048452581 7130101003994519634084859)
        ·
          refine ⟨10695151505991779451127289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7130101003994519634084859 10695151505991779451127289)
          ·
            refine ⟨8021363629493834588345467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10695151505991779451127289 8021363629493834588345467)
            ·
              refine ⟨12032045444240751882518201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8021363629493834588345467 12032045444240751882518201)
              ·
                refine ⟨9024034083180563911888651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12032045444240751882518201 9024034083180563911888651)
                ·
                  refine ⟨13536051124770845867832977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9024034083180563911888651 13536051124770845867832977)
                  ·
                    refine ⟨10152038343578134400874733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13536051124770845867832977 10152038343578134400874733)
                    ·
                      refine ⟨3807014378841800400328025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10152038343578134400874733 3807014378841800400328025)
                      ·
                        rfl

theorem cell23_7414134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 2, 1, 2, 1, 2, 3].length) (baseStart_7414134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7414134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7414134 prefixEnd_7414134 := by exact prefixLift 7414134
  have htrace : WordTrace (prefixWord ++ tailWord_7414134) baseStart_7414134 baseEnd_7414134 := by
    simpa [prefixWord, tailWord_7414134, baseEnd_7414134] using wordTrace_append hprefix tailTrace_7414134
  have hstable : (prefixWord ++ tailWord_7414134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7414134).length < 2 ^ (prefixWord ++ tailWord_7414134).sum := by decide
  have hdescent : baseEnd_7414134 < baseStart_7414134 := by decide
  rcases family_descends (prefixWord ++ tailWord_7414134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7414153 : List Nat := [1, 2, 1, 1, 6, 1, 1, 1, 3, 4, 2]
def baseStart_7414153 : Nat := 118140960795 + 7414153 * 2 ^ 59
def prefixEnd_7414153 : Nat := 4983230072969 + 3 ^ 40 * 7414153 * 2
def baseEnd_7414153 : Nat := 3807024134974235825990437

theorem tailTrace_7414153 : CollatzResearch.WordTrace tailWord_7414153 prefixEnd_7414153 3807024134974235825990437 := by
  unfold tailWord_7414153
  simp only [CollatzResearch.WordTrace]
  refine ⟨270416375508797392367271113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180277583672531594911514075 270416375508797392367271113)
  ·
    refine ⟨202812281631598044275453335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 270416375508797392367271113 202812281631598044275453335)
    ·
      refine ⟨304218422447397066413180003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202812281631598044275453335 304218422447397066413180003)
      ·
        refine ⟨456327633671095599619770005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 304218422447397066413180003 456327633671095599619770005)
        ·
          refine ⟨21390357828332606232176719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 456327633671095599619770005 21390357828332606232176719)
          ·
            refine ⟨32085536742498909348265079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21390357828332606232176719 32085536742498909348265079)
            ·
              refine ⟨48128305113748364022397619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32085536742498909348265079 48128305113748364022397619)
              ·
                refine ⟨72192457670622546033596429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48128305113748364022397619 72192457670622546033596429)
                ·
                  refine ⟨27072171626483454762598661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 72192457670622546033596429 27072171626483454762598661)
                  ·
                    refine ⟨5076032179965647767987249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27072171626483454762598661 5076032179965647767987249)
                    ·
                      refine ⟨3807024134974235825990437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5076032179965647767987249 3807024134974235825990437)
                      ·
                        rfl

theorem cell23_7414153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 1, 1, 3, 4, 2].length) (baseStart_7414153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7414153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7414153 prefixEnd_7414153 := by exact prefixLift 7414153
  have htrace : WordTrace (prefixWord ++ tailWord_7414153) baseStart_7414153 baseEnd_7414153 := by
    simpa [prefixWord, tailWord_7414153, baseEnd_7414153] using wordTrace_append hprefix tailTrace_7414153
  have hstable : (prefixWord ++ tailWord_7414153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7414153).length < 2 ^ (prefixWord ++ tailWord_7414153).sum := by decide
  have hdescent : baseEnd_7414153 < baseStart_7414153 := by decide
  rcases family_descends (prefixWord ++ tailWord_7414153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7414156 : List Nat := [2, 2, 1, 2, 1, 4, 2, 1, 2, 1, 5]
def baseStart_7414156 : Nat := 118140960795 + 7414156 * 2 ^ 59
def prefixEnd_7414156 : Nat := 4983230072969 + 3 ^ 40 * 7414156 * 2
def baseEnd_7414156 : Nat := 3807025675416199314252923

theorem tailTrace_7414156 : CollatzResearch.WordTrace tailWord_7414156 prefixEnd_7414156 3807025675416199314252923 := by
  unfold tailWord_7414156
  simp only [CollatzResearch.WordTrace]
  refine ⟨135208242463893261939815161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180277656618524349253086881 135208242463893261939815161)
  ·
    refine ⟨101406181847919946454861371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135208242463893261939815161 101406181847919946454861371)
    ·
      refine ⟨152109272771879919682292057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101406181847919946454861371 152109272771879919682292057)
      ·
        refine ⟨114081954578909939761719043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 152109272771879919682292057 114081954578909939761719043)
        ·
          refine ⟨171122931868364909642578565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114081954578909939761719043 171122931868364909642578565)
          ·
            refine ⟨32085549725318420557983481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 171122931868364909642578565 32085549725318420557983481)
            ·
              refine ⟨24064162293988815418487611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32085549725318420557983481 24064162293988815418487611)
              ·
                refine ⟨36096243440983223127731417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24064162293988815418487611 36096243440983223127731417)
                ·
                  refine ⟨27072182580737417345798563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36096243440983223127731417 27072182580737417345798563)
                  ·
                    refine ⟨40608273871106126018697845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27072182580737417345798563 40608273871106126018697845)
                    ·
                      refine ⟨3807025675416199314252923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40608273871106126018697845 3807025675416199314252923)
                      ·
                        rfl

theorem cell23_7414156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 2, 1, 2, 1, 5].length) (baseStart_7414156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7414156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7414156 prefixEnd_7414156 := by exact prefixLift 7414156
  have htrace : WordTrace (prefixWord ++ tailWord_7414156) baseStart_7414156 baseEnd_7414156 := by
    simpa [prefixWord, tailWord_7414156, baseEnd_7414156] using wordTrace_append hprefix tailTrace_7414156
  have hstable : (prefixWord ++ tailWord_7414156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7414156).length < 2 ^ (prefixWord ++ tailWord_7414156).sum := by decide
  have hdescent : baseEnd_7414156 < baseStart_7414156 := by decide
  rcases family_descends (prefixWord ++ tailWord_7414156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7414183 : List Nat := [1, 1, 6, 1, 1, 3, 1, 1, 2, 2, 4]
def baseStart_7414183 : Nat := 118140960795 + 7414183 * 2 ^ 59
def prefixEnd_7414183 : Nat := 4983230072969 + 3 ^ 40 * 7414183 * 2
def baseEnd_7414183 : Nat := 3807039539393870708615299

theorem tailTrace_7414183 : CollatzResearch.WordTrace tailWord_7414183 prefixEnd_7414183 3807039539393870708615299 := by
  unfold tailWord_7414183
  simp only [CollatzResearch.WordTrace]
  refine ⟨270417469698688707490863203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180278313132459138327242135 270417469698688707490863203)
  ·
    refine ⟨405626204548033061236294805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270417469698688707490863203 405626204548033061236294805)
    ·
      refine ⟨19013728338189049745451319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 405626204548033061236294805 19013728338189049745451319)
      ·
        refine ⟨28520592507283574618176979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19013728338189049745451319 28520592507283574618176979)
        ·
          refine ⟨42780888760925361927265469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28520592507283574618176979 42780888760925361927265469)
          ·
            refine ⟨16042833285347010722724551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42780888760925361927265469 16042833285347010722724551)
            ·
              refine ⟨24064249928020516084086827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16042833285347010722724551 24064249928020516084086827)
              ·
                refine ⟨36096374892030774126130241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24064249928020516084086827 36096374892030774126130241)
                ·
                  refine ⟨27072281169023080594597681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36096374892030774126130241 27072281169023080594597681)
                  ·
                    refine ⟨20304210876767310445948261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27072281169023080594597681 20304210876767310445948261)
                    ·
                      refine ⟨3807039539393870708615299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20304210876767310445948261 3807039539393870708615299)
                      ·
                        rfl

theorem cell23_7414183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 1, 1, 2, 2, 4].length) (baseStart_7414183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7414183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7414183 prefixEnd_7414183 := by exact prefixLift 7414183
  have htrace : WordTrace (prefixWord ++ tailWord_7414183) baseStart_7414183 baseEnd_7414183 := by
    simpa [prefixWord, tailWord_7414183, baseEnd_7414183] using wordTrace_append hprefix tailTrace_7414183
  have hstable : (prefixWord ++ tailWord_7414183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7414183).length < 2 ^ (prefixWord ++ tailWord_7414183).sum := by decide
  have hdescent : baseEnd_7414183 < baseStart_7414183 := by decide
  rcases family_descends (prefixWord ++ tailWord_7414183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7414256 : List Nat := [2, 1, 1, 1, 3, 3, 1, 1, 2, 4, 4]
def baseStart_7414256 : Nat := 118140960795 + 7414256 * 2 ^ 59
def prefixEnd_7414256 : Nat := 4983230072969 + 3 ^ 40 * 7414256 * 2
def baseEnd_7414256 : Nat := 3807077023481648923002463

theorem tailTrace_7414256 : CollatzResearch.WordTrace tailWord_7414256 prefixEnd_7414256 3807077023481648923002463 := by
  unfold tailWord_7414256
  simp only [CollatzResearch.WordTrace]
  refine ⟨135210066113712120479135311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180280088151616160638847081 135210066113712120479135311)
  ·
    refine ⟨202815099170568180718702967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135210066113712120479135311 202815099170568180718702967)
    ·
      refine ⟨304222648755852271078054451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202815099170568180718702967 304222648755852271078054451)
      ·
        refine ⟨456333973133778406617081677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 304222648755852271078054451 456333973133778406617081677)
        ·
          refine ⟨171125239925166902481405629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 456333973133778406617081677 171125239925166902481405629)
          ·
            refine ⟨64171964971937588430527111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 171125239925166902481405629 64171964971937588430527111)
            ·
              refine ⟨96257947457906382645790667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64171964971937588430527111 96257947457906382645790667)
              ·
                refine ⟨144386921186859573968686001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 96257947457906382645790667 144386921186859573968686001)
                ·
                  refine ⟨108290190890144680476514501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 144386921186859573968686001 108290190890144680476514501)
                  ·
                    refine ⟨20304410791902127589346469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 108290190890144680476514501 20304410791902127589346469)
                    ·
                      refine ⟨3807077023481648923002463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20304410791902127589346469 3807077023481648923002463)
                      ·
                        rfl

theorem cell23_7414256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 1, 2, 4, 4].length) (baseStart_7414256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7414256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7414256 prefixEnd_7414256 := by exact prefixLift 7414256
  have htrace : WordTrace (prefixWord ++ tailWord_7414256) baseStart_7414256 baseEnd_7414256 := by
    simpa [prefixWord, tailWord_7414256, baseEnd_7414256] using wordTrace_append hprefix tailTrace_7414256
  have hstable : (prefixWord ++ tailWord_7414256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7414256).length < 2 ^ (prefixWord ++ tailWord_7414256).sum := by decide
  have hdescent : baseEnd_7414256 < baseStart_7414256 := by decide
  rcases family_descends (prefixWord ++ tailWord_7414256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7414300 : List Nat := [2, 2, 3, 1, 2, 2, 4, 1, 6]
def baseStart_7414300 : Nat := 118140960795 + 7414300 * 2 ^ 59
def prefixEnd_7414300 : Nat := 4983230072969 + 3 ^ 40 * 7414300 * 2
def baseEnd_7414300 : Nat := 423011068514494083428029

theorem tailTrace_7414300 : CollatzResearch.WordTrace tailWord_7414300 prefixEnd_7414300 423011068514494083428029 := by
  unfold tailWord_7414300
  simp only [CollatzResearch.WordTrace]
  refine ⟨135210868519632418236436177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180281158026176557648581569 135210868519632418236436177)
  ·
    refine ⟨101408151389724313677327133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135210868519632418236436177 101408151389724313677327133)
    ·
      refine ⟨38028056771146617628997675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 101408151389724313677327133 38028056771146617628997675)
      ·
        refine ⟨57042085156719926443496513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38028056771146617628997675 57042085156719926443496513)
        ·
          refine ⟨42781563867539944832622385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57042085156719926443496513 42781563867539944832622385)
          ·
            refine ⟨32086172900654958624466789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42781563867539944832622385 32086172900654958624466789)
            ·
              refine ⟨6016157418872804742087523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32086172900654958624466789 6016157418872804742087523)
              ·
                refine ⟨9024236128309207113131285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6016157418872804742087523 9024236128309207113131285)
                ·
                  refine ⟨423011068514494083428029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9024236128309207113131285 423011068514494083428029)
                  ·
                    rfl

theorem cell23_7414300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 4, 1, 6].length) (baseStart_7414300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7414300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7414300 prefixEnd_7414300 := by exact prefixLift 7414300
  have htrace : WordTrace (prefixWord ++ tailWord_7414300) baseStart_7414300 baseEnd_7414300 := by
    simpa [prefixWord, tailWord_7414300, baseEnd_7414300] using wordTrace_append hprefix tailTrace_7414300
  have hstable : (prefixWord ++ tailWord_7414300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7414300).length < 2 ^ (prefixWord ++ tailWord_7414300).sum := by decide
  have hdescent : baseEnd_7414300 < baseStart_7414300 := by decide
  rcases family_descends (prefixWord ++ tailWord_7414300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7414320 : List Nat := [2, 1, 1, 1, 2, 3, 3, 3, 2, 3, 2]
def baseStart_7414320 : Nat := 118140960795 + 7414320 * 2 ^ 59
def prefixEnd_7414320 : Nat := 4983230072969 + 3 ^ 40 * 7414320 * 2
def baseEnd_7414320 : Nat := 3807109886243536672602169

theorem tailTrace_7414320 : CollatzResearch.WordTrace tailWord_7414320 prefixEnd_7414320 3807109886243536672602169 := by
  unfold tailWord_7414320
  simp only [CollatzResearch.WordTrace]
  refine ⟨135211233249596189944300207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180281644332794919925733609 135211233249596189944300207)
  ·
    refine ⟨202816849874394284916450311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135211233249596189944300207 202816849874394284916450311)
    ·
      refine ⟨304225274811591427374675467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202816849874394284916450311 304225274811591427374675467)
      ·
        refine ⟨456337912217387141062013201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 304225274811591427374675467 456337912217387141062013201)
        ·
          refine ⟨342253434163040355796509901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 456337912217387141062013201 342253434163040355796509901)
          ·
            refine ⟨128345037811140133423691213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 342253434163040355796509901 128345037811140133423691213)
            ·
              refine ⟨48129389179177550033884205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 128345037811140133423691213 48129389179177550033884205)
              ·
                refine ⟨18048520942191581262706577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48129389179177550033884205 18048520942191581262706577)
                ·
                  refine ⟨13536390706643685947029933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18048520942191581262706577 13536390706643685947029933)
                  ·
                    refine ⟨5076146514991382230136225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13536390706643685947029933 5076146514991382230136225)
                    ·
                      refine ⟨3807109886243536672602169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5076146514991382230136225 3807109886243536672602169)
                      ·
                        rfl

theorem cell23_7414320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 3, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 3, 3, 2, 3, 2].length) (baseStart_7414320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7414320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7414320 prefixEnd_7414320 := by exact prefixLift 7414320
  have htrace : WordTrace (prefixWord ++ tailWord_7414320) baseStart_7414320 baseEnd_7414320 := by
    simpa [prefixWord, tailWord_7414320, baseEnd_7414320] using wordTrace_append hprefix tailTrace_7414320
  have hstable : (prefixWord ++ tailWord_7414320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7414320).length < 2 ^ (prefixWord ++ tailWord_7414320).sum := by decide
  have hdescent : baseEnd_7414320 < baseStart_7414320 := by decide
  rcases family_descends (prefixWord ++ tailWord_7414320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7414327 : List Nat := [1, 1, 3, 1, 2, 3, 2, 5, 1, 1, 3]
def baseStart_7414327 : Nat := 118140960795 + 7414327 * 2 ^ 59
def prefixEnd_7414327 : Nat := 4983230072969 + 3 ^ 40 * 7414327 * 2
def baseEnd_7414327 : Nat := 3807113480608118145214637

theorem tailTrace_7414327 : CollatzResearch.WordTrace tailWord_7414327 prefixEnd_7414327 3807113480608118145214637 := by
  unfold tailWord_7414327
  simp only [CollatzResearch.WordTrace]
  refine ⟨270422721810167020084105235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180281814540111346722736823 270422721810167020084105235)
  ·
    refine ⟨405634082715250530126157853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270422721810167020084105235 405634082715250530126157853)
    ·
      refine ⟨152112781018218948797309195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 405634082715250530126157853 152112781018218948797309195)
      ·
        refine ⟨228169171527328423195963793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152112781018218948797309195 228169171527328423195963793)
        ·
          refine ⟨171126878645496317396972845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 228169171527328423195963793 171126878645496317396972845)
          ·
            refine ⟨64172579492061119023864817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 171126878645496317396972845 64172579492061119023864817)
            ·
              refine ⟨48129434619045839267898613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64172579492061119023864817 48129434619045839267898613)
              ·
                refine ⟨4512134495535547431365495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 48129434619045839267898613 4512134495535547431365495)
                ·
                  refine ⟨6768201743303321147048243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4512134495535547431365495 6768201743303321147048243)
                  ·
                    refine ⟨10152302614954981720572365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6768201743303321147048243 10152302614954981720572365)
                    ·
                      refine ⟨3807113480608118145214637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10152302614954981720572365 3807113480608118145214637)
                      ·
                        rfl

theorem cell23_7414327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 2, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 2, 5, 1, 1, 3].length) (baseStart_7414327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7414327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7414327 prefixEnd_7414327 := by exact prefixLift 7414327
  have htrace : WordTrace (prefixWord ++ tailWord_7414327) baseStart_7414327 baseEnd_7414327 := by
    simpa [prefixWord, tailWord_7414327, baseEnd_7414327] using wordTrace_append hprefix tailTrace_7414327
  have hstable : (prefixWord ++ tailWord_7414327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7414327).length < 2 ^ (prefixWord ++ tailWord_7414327).sum := by decide
  have hdescent : baseEnd_7414327 < baseStart_7414327 := by decide
  rcases family_descends (prefixWord ++ tailWord_7414327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7414337 : List Nat := [1, 2, 5, 1, 1, 2, 2, 2, 2, 3, 2]
def baseStart_7414337 : Nat := 118140960795 + 7414337 * 2 ^ 59
def prefixEnd_7414337 : Nat := 4983230072969 + 3 ^ 40 * 7414337 * 2
def baseEnd_7414337 : Nat := 3807118615414663106089591

theorem tailTrace_7414337 : CollatzResearch.WordTrace tailWord_7414337 prefixEnd_7414337 3807118615414663106089591 := by
  unfold tailWord_7414337
  simp only [CollatzResearch.WordTrace]
  refine ⟨270423086540130791791969265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180282057693420527861312843 270423086540130791791969265)
  ·
    refine ⟨202817314905098093843976949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 270423086540130791791969265 202817314905098093843976949)
    ·
      refine ⟨19014123272352946297872839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 202817314905098093843976949 19014123272352946297872839)
      ·
        refine ⟨28521184908529419446809259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19014123272352946297872839 28521184908529419446809259)
        ·
          refine ⟨42781777362794129170213889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28521184908529419446809259 42781777362794129170213889)
          ·
            refine ⟨32086333022095596877660417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42781777362794129170213889 32086333022095596877660417)
            ·
              refine ⟨24064749766571697658245313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32086333022095596877660417 24064749766571697658245313)
              ·
                refine ⟨18048562324928773243683985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24064749766571697658245313 18048562324928773243683985)
                ·
                  refine ⟨13536421743696579932762989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18048562324928773243683985 13536421743696579932762989)
                  ·
                    refine ⟨5076158153886217474786121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13536421743696579932762989 5076158153886217474786121)
                    ·
                      refine ⟨3807118615414663106089591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5076158153886217474786121 3807118615414663106089591)
                      ·
                        rfl

theorem cell23_7414337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 2, 2, 2, 3, 2].length) (baseStart_7414337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7414337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7414337 prefixEnd_7414337 := by exact prefixLift 7414337
  have htrace : WordTrace (prefixWord ++ tailWord_7414337) baseStart_7414337 baseEnd_7414337 := by
    simpa [prefixWord, tailWord_7414337, baseEnd_7414337] using wordTrace_append hprefix tailTrace_7414337
  have hstable : (prefixWord ++ tailWord_7414337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7414337).length < 2 ^ (prefixWord ++ tailWord_7414337).sum := by decide
  have hdescent : baseEnd_7414337 < baseStart_7414337 := by decide
  rcases family_descends (prefixWord ++ tailWord_7414337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7414360 : List Nat := [2, 1, 2, 2, 1, 2, 4, 3, 2, 4]
def baseStart_7414360 : Nat := 118140960795 + 7414360 * 2 ^ 59
def prefixEnd_7414360 : Nat := 4983230072969 + 3 ^ 40 * 7414360 * 2
def baseEnd_7414360 : Nat := 1269043475156572172033995

theorem tailTrace_7414360 : CollatzResearch.WordTrace tailWord_7414360 prefixEnd_7414360 1269043475156572172033995 := by
  unfold tailWord_7414360
  simp only [CollatzResearch.WordTrace]
  refine ⟨135211962709523733360028267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180282616946031644480037689 135211962709523733360028267)
  ·
    refine ⟨202817944064285600040042401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135211962709523733360028267 202817944064285600040042401)
    ·
      refine ⟨152113458048214200030031801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 202817944064285600040042401 152113458048214200030031801)
      ·
        refine ⟨114085093536160650022523851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 152113458048214200030031801 114085093536160650022523851)
        ·
          refine ⟨171127640304240975033785777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114085093536160650022523851 171127640304240975033785777)
          ·
            refine ⟨128345730228180731275339333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 171127640304240975033785777 128345730228180731275339333)
            ·
              refine ⟨24064824417783887114126125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 128345730228180731275339333 24064824417783887114126125)
              ·
                refine ⟨9024309156668957667797297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24064824417783887114126125 9024309156668957667797297)
                ·
                  refine ⟨6768231867501718250847973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9024309156668957667797297 6768231867501718250847973)
                  ·
                    refine ⟨1269043475156572172033995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6768231867501718250847973 1269043475156572172033995)
                    ·
                      rfl

theorem cell23_7414360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 4, 3, 2, 4].length) (baseStart_7414360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7414360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7414360 prefixEnd_7414360 := by exact prefixLift 7414360
  have htrace : WordTrace (prefixWord ++ tailWord_7414360) baseStart_7414360 baseEnd_7414360 := by
    simpa [prefixWord, tailWord_7414360, baseEnd_7414360] using wordTrace_append hprefix tailTrace_7414360
  have hstable : (prefixWord ++ tailWord_7414360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7414360).length < 2 ^ (prefixWord ++ tailWord_7414360).sum := by decide
  have hdescent : baseEnd_7414360 < baseStart_7414360 := by decide
  rcases family_descends (prefixWord ++ tailWord_7414360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7414384 : List Nat := [2, 1, 1, 1, 7, 2, 2, 1, 1, 1, 4]
def baseStart_7414384 : Nat := 118140960795 + 7414384 * 2 ^ 59
def prefixEnd_7414384 : Nat := 4983230072969 + 3 ^ 40 * 7414384 * 2
def baseEnd_7414384 : Nat := 3807142749005424422201875

theorem tailTrace_7414384 : CollatzResearch.WordTrace tailWord_7414384 prefixEnd_7414384 3807142749005424422201875 := by
  unfold tailWord_7414384
  simp only [CollatzResearch.WordTrace]
  refine ⟨135212400385480259409465103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180283200513973679212620137 135212400385480259409465103)
  ·
    refine ⟨202818600578220389114197655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135212400385480259409465103 202818600578220389114197655)
    ·
      refine ⟨304227900867330583671296483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202818600578220389114197655 304227900867330583671296483)
      ·
        refine ⟨456341851300995875506944725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 304227900867330583671296483 456341851300995875506944725)
        ·
          refine ⟨10695512139867090832194017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 456341851300995875506944725 10695512139867090832194017)
          ·
            refine ⟨8021634104900318124145513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10695512139867090832194017 8021634104900318124145513)
            ·
              refine ⟨6016225578675238593109135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8021634104900318124145513 6016225578675238593109135)
              ·
                refine ⟨9024338368012857889663703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6016225578675238593109135 9024338368012857889663703)
                ·
                  refine ⟨13536507552019286834495555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9024338368012857889663703 13536507552019286834495555)
                  ·
                    refine ⟨20304761328028930251743333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13536507552019286834495555 20304761328028930251743333)
                    ·
                      refine ⟨3807142749005424422201875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20304761328028930251743333 3807142749005424422201875)
                      ·
                        rfl

theorem cell23_7414384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 2, 2, 1, 1, 1, 4].length) (baseStart_7414384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7414384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7414384 prefixEnd_7414384 := by exact prefixLift 7414384
  have htrace : WordTrace (prefixWord ++ tailWord_7414384) baseStart_7414384 baseEnd_7414384 := by
    simpa [prefixWord, tailWord_7414384, baseEnd_7414384] using wordTrace_append hprefix tailTrace_7414384
  have hstable : (prefixWord ++ tailWord_7414384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7414384).length < 2 ^ (prefixWord ++ tailWord_7414384).sum := by decide
  have hdescent : baseEnd_7414384 < baseStart_7414384 := by decide
  rcases family_descends (prefixWord ++ tailWord_7414384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7414390 : List Nat := [5, 1, 1, 2, 3, 1, 10]
def baseStart_7414390 : Nat := 118140960795 + 7414390 * 2 ^ 59
def prefixEnd_7414390 : Nat := 4983230072969 + 3 ^ 40 * 7414390 * 2
def baseEnd_7414390 : Nat := 47001800369004338255887

theorem tailTrace_7414390 : CollatzResearch.WordTrace tailWord_7414390 prefixEnd_7414390 47001800369004338255887 := by
  unfold tailWord_7414390
  simp only [CollatzResearch.WordTrace]
  refine ⟨16901563725558673865228039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 180283346405959187895765749 16901563725558673865228039)
  ·
    refine ⟨25352345588338010797842059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16901563725558673865228039 25352345588338010797842059)
    ·
      refine ⟨38028518382507016196763089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25352345588338010797842059 38028518382507016196763089)
      ·
        refine ⟨28521388786880262147572317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38028518382507016196763089 28521388786880262147572317)
        ·
          refine ⟨10695520795080098305339619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28521388786880262147572317 10695520795080098305339619)
          ·
            refine ⟨16043281192620147458009429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10695520795080098305339619 16043281192620147458009429)
            ·
              refine ⟨47001800369004338255887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 16043281192620147458009429 47001800369004338255887)
              ·
                rfl

theorem cell23_7414390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 10].length) (baseStart_7414390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7414390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7414390 prefixEnd_7414390 := by exact prefixLift 7414390
  have htrace : WordTrace (prefixWord ++ tailWord_7414390) baseStart_7414390 baseEnd_7414390 := by
    simpa [prefixWord, tailWord_7414390, baseEnd_7414390] using wordTrace_append hprefix tailTrace_7414390
  have hstable : (prefixWord ++ tailWord_7414390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7414390).length < 2 ^ (prefixWord ++ tailWord_7414390).sum := by decide
  have hdescent : baseEnd_7414390 < baseStart_7414390 := by decide
  rcases family_descends (prefixWord ++ tailWord_7414390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7414430 : List Nat := [4, 3, 1, 1, 1, 1, 1, 1, 1, 4, 5]
def baseStart_7414430 : Nat := 118140960795 + 7414430 * 2 ^ 59
def prefixEnd_7414430 : Nat := 4983230072969 + 3 ^ 40 * 7414430 * 2
def baseEnd_7414430 : Nat := 3807166369115531242226663

theorem tailTrace_7414430 : CollatzResearch.WordTrace tailWord_7414430 prefixEnd_7414430 3807166369115531242226663 := by
  unfold tailWord_7414430
  simp only [CollatzResearch.WordTrace]
  refine ⟨33803309816099233584388093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 180284319019195912450069829 33803309816099233584388093)
  ·
    refine ⟨12676241181037212594145535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33803309816099233584388093 12676241181037212594145535)
    ·
      refine ⟨19014361771555818891218303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12676241181037212594145535 19014361771555818891218303)
      ·
        refine ⟨28521542657333728336827455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19014361771555818891218303 28521542657333728336827455)
        ·
          refine ⟨42782313986000592505241183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28521542657333728336827455 42782313986000592505241183)
          ·
            refine ⟨64173470979000888757861775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42782313986000592505241183 64173470979000888757861775)
            ·
              refine ⟨96260206468501333136792663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64173470979000888757861775 96260206468501333136792663)
              ·
                refine ⟨144390309702751999705188995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 96260206468501333136792663 144390309702751999705188995)
                ·
                  refine ⟨216585464554127999557783493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 144390309702751999705188995 216585464554127999557783493)
                  ·
                    refine ⟨40609774603898999917084405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 216585464554127999557783493 40609774603898999917084405)
                    ·
                      refine ⟨3807166369115531242226663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40609774603898999917084405 3807166369115531242226663)
                      ·
                        rfl

theorem cell23_7414430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 1, 1, 4, 5].length) (baseStart_7414430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7414430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7414430 prefixEnd_7414430 := by exact prefixLift 7414430
  have htrace : WordTrace (prefixWord ++ tailWord_7414430) baseStart_7414430 baseEnd_7414430 := by
    simpa [prefixWord, tailWord_7414430, baseEnd_7414430] using wordTrace_append hprefix tailTrace_7414430
  have hstable : (prefixWord ++ tailWord_7414430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7414430).length < 2 ^ (prefixWord ++ tailWord_7414430).sum := by decide
  have hdescent : baseEnd_7414430 < baseStart_7414430 := by decide
  rcases family_descends (prefixWord ++ tailWord_7414430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7414460 : List Nat := [2, 2, 2, 3, 1, 1, 2, 1, 2, 4, 3]
def baseStart_7414460 : Nat := 118140960795 + 7414460 * 2 ^ 59
def prefixEnd_7414460 : Nat := 4983230072969 + 3 ^ 40 * 7414460 * 2
def baseEnd_7414460 : Nat := 3807181773535166124851525

theorem tailTrace_7414460 : CollatzResearch.WordTrace tailWord_7414460 prefixEnd_7414460 3807181773535166124851525 := by
  unfold tailWord_7414460
  simp only [CollatzResearch.WordTrace]
  refine ⟨135213786359342591899348417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180285048479123455865797889 135213786359342591899348417)
  ·
    refine ⟨101410339769506943924511313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135213786359342591899348417 101410339769506943924511313)
    ·
      refine ⟨76057754827130207943383485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101410339769506943924511313 76057754827130207943383485)
      ·
        refine ⟨28521658060173827978768807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76057754827130207943383485 28521658060173827978768807)
        ·
          refine ⟨42782487090260741968153211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28521658060173827978768807 42782487090260741968153211)
          ·
            refine ⟨64173730635391112952229817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42782487090260741968153211 64173730635391112952229817)
            ·
              refine ⟨48130297976543334714172363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64173730635391112952229817 48130297976543334714172363)
              ·
                refine ⟨72195446964815002071258545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48130297976543334714172363 72195446964815002071258545)
                ·
                  refine ⟨54146585223611251553443909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 72195446964815002071258545 54146585223611251553443909)
                  ·
                    refine ⟨10152484729427109666270733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 54146585223611251553443909 10152484729427109666270733)
                    ·
                      refine ⟨3807181773535166124851525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10152484729427109666270733 3807181773535166124851525)
                      ·
                        rfl

theorem cell23_7414460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 2, 1, 2, 4, 3].length) (baseStart_7414460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7414460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7414460 prefixEnd_7414460 := by exact prefixLift 7414460
  have htrace : WordTrace (prefixWord ++ tailWord_7414460) baseStart_7414460 baseEnd_7414460 := by
    simpa [prefixWord, tailWord_7414460, baseEnd_7414460] using wordTrace_append hprefix tailTrace_7414460
  have hstable : (prefixWord ++ tailWord_7414460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7414460).length < 2 ^ (prefixWord ++ tailWord_7414460).sum := by decide
  have hdescent : baseEnd_7414460 < baseStart_7414460 := by decide
  rcases family_descends (prefixWord ++ tailWord_7414460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7414514 : List Nat := [3, 2, 1, 3, 1, 2, 4, 2, 5]
def baseStart_7414514 : Nat := 118140960795 + 7414514 * 2 ^ 59
def prefixEnd_7414514 : Nat := 4983230072969 + 3 ^ 40 * 7414514 * 2
def baseEnd_7414514 : Nat := 423023277943389879286253

theorem tailTrace_7414514 : CollatzResearch.WordTrace tailWord_7414514 prefixEnd_7414514 423023277943389879286253 := by
  unfold tailWord_7414514
  simp only [CollatzResearch.WordTrace]
  refine ⟨67607385565122387755290649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 180286361506993034014108397 67607385565122387755290649)
  ·
    refine ⟨50705539173841790816467987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67607385565122387755290649 50705539173841790816467987)
    ·
      refine ⟨76058308760762686224701981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50705539173841790816467987 76058308760762686224701981)
      ·
        refine ⟨28521865785286007334263243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76058308760762686224701981 28521865785286007334263243)
        ·
          refine ⟨42782798677929011001394865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28521865785286007334263243 42782798677929011001394865)
          ·
            refine ⟨32087099008446758251046149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42782798677929011001394865 32087099008446758251046149)
            ·
              refine ⟨6016331064083767172071153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32087099008446758251046149 6016331064083767172071153)
              ·
                refine ⟨4512248298062825379053365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6016331064083767172071153 4512248298062825379053365)
                ·
                  refine ⟨423023277943389879286253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4512248298062825379053365 423023277943389879286253)
                  ·
                    rfl

theorem cell23_7414514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 4, 2, 5].length) (baseStart_7414514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7414514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7414514 prefixEnd_7414514 := by exact prefixLift 7414514
  have htrace : WordTrace (prefixWord ++ tailWord_7414514) baseStart_7414514 baseEnd_7414514 := by
    simpa [prefixWord, tailWord_7414514, baseEnd_7414514] using wordTrace_append hprefix tailTrace_7414514
  have hstable : (prefixWord ++ tailWord_7414514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7414514).length < 2 ^ (prefixWord ++ tailWord_7414514).sum := by decide
  have hdescent : baseEnd_7414514 < baseStart_7414514 := by decide
  rcases family_descends (prefixWord ++ tailWord_7414514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7414560 : List Nat := [2, 1, 1, 5, 1, 2, 1, 1, 2, 1, 6]
def baseStart_7414560 : Nat := 118140960795 + 7414560 * 2 ^ 59
def prefixEnd_7414560 : Nat := 4983230072969 + 3 ^ 40 * 7414560 * 2
def baseEnd_7414560 : Nat := 3807233121600615733601065

theorem tailTrace_7414560 : CollatzResearch.WordTrace tailWord_7414560 prefixEnd_7414560 3807233121600615733601065 := by
  unfold tailWord_7414560
  simp only [CollatzResearch.WordTrace]
  refine ⟨135215610009161450438668567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180287480012215267251558089 135215610009161450438668567)
  ·
    refine ⟨202823415013742175658002851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135215610009161450438668567 202823415013742175658002851)
    ·
      refine ⟨304235122520613263487004277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202823415013742175658002851 304235122520613263487004277)
      ·
        refine ⟨28522042736307493451906651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 304235122520613263487004277 28522042736307493451906651)
        ·
          refine ⟨42783064104461240177859977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28522042736307493451906651 42783064104461240177859977)
          ·
            refine ⟨32087298078345930133394983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42783064104461240177859977 32087298078345930133394983)
            ·
              refine ⟨48130947117518895200092475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32087298078345930133394983 48130947117518895200092475)
              ·
                refine ⟨72196420676278342800138713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48130947117518895200092475 72196420676278342800138713)
                ·
                  refine ⟨54147315507208757100104035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 72196420676278342800138713 54147315507208757100104035)
                  ·
                    refine ⟨81220973260813135650156053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 54147315507208757100104035 81220973260813135650156053)
                    ·
                      refine ⟨3807233121600615733601065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 81220973260813135650156053 3807233121600615733601065)
                      ·
                        rfl

theorem cell23_7414560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 1, 1, 2, 1, 6].length) (baseStart_7414560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7414560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7414560 prefixEnd_7414560 := by exact prefixLift 7414560
  have htrace : WordTrace (prefixWord ++ tailWord_7414560) baseStart_7414560 baseEnd_7414560 := by
    simpa [prefixWord, tailWord_7414560, baseEnd_7414560] using wordTrace_append hprefix tailTrace_7414560
  have hstable : (prefixWord ++ tailWord_7414560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7414560).length < 2 ^ (prefixWord ++ tailWord_7414560).sum := by decide
  have hdescent : baseEnd_7414560 < baseStart_7414560 := by decide
  rcases family_descends (prefixWord ++ tailWord_7414560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7414574 : List Nat := [4, 1, 3, 2, 1, 1, 1, 3, 3, 4]
def baseStart_7414574 : Nat := 118140960795 + 7414574 * 2 ^ 59
def prefixEnd_7414574 : Nat := 4983230072969 + 3 ^ 40 * 7414574 * 2
def baseEnd_7414574 : Nat := 1269080103443259559608667

theorem tailTrace_7414574 : CollatzResearch.WordTrace tailWord_7414574 prefixEnd_7414574 1269080103443259559608667 := by
  unfold tailWord_7414574
  simp only [CollatzResearch.WordTrace]
  refine ⟨33803966330034022658543347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 180287820426848120845564517 33803966330034022658543347)
  ·
    refine ⟨50705949495051033987815021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33803966330034022658543347 50705949495051033987815021)
    ·
      refine ⟨19014731060644137745430633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50705949495051033987815021 19014731060644137745430633)
      ·
        refine ⟨14261048295483103309072975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19014731060644137745430633 14261048295483103309072975)
        ·
          refine ⟨21391572443224654963609463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14261048295483103309072975 21391572443224654963609463)
          ·
            refine ⟨32087358664836982445414195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21391572443224654963609463 32087358664836982445414195)
            ·
              refine ⟨48131037997255473668121293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32087358664836982445414195 48131037997255473668121293)
              ·
                refine ⟨18049139248970802625545485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48131037997255473668121293 18049139248970802625545485)
                ·
                  refine ⟨6768427218364050984579557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18049139248970802625545485 6768427218364050984579557)
                  ·
                    refine ⟨1269080103443259559608667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6768427218364050984579557 1269080103443259559608667)
                    ·
                      rfl

theorem cell23_7414574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 1, 3, 3, 4].length) (baseStart_7414574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7414574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7414574 prefixEnd_7414574 := by exact prefixLift 7414574
  have htrace : WordTrace (prefixWord ++ tailWord_7414574) baseStart_7414574 baseEnd_7414574 := by
    simpa [prefixWord, tailWord_7414574, baseEnd_7414574] using wordTrace_append hprefix tailTrace_7414574
  have hstable : (prefixWord ++ tailWord_7414574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7414574).length < 2 ^ (prefixWord ++ tailWord_7414574).sum := by decide
  have hdescent : baseEnd_7414574 < baseStart_7414574 := by decide
  rcases family_descends (prefixWord ++ tailWord_7414574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7414597 : List Nat := [1, 3, 1, 1, 1, 2, 2, 3, 5, 1, 3]
def baseStart_7414597 : Nat := 118140960795 + 7414597 * 2 ^ 59
def prefixEnd_7414597 : Nat := 4983230072969 + 3 ^ 40 * 7414597 * 2
def baseEnd_7414597 : Nat := 3807252120384832088838395

theorem tailTrace_7414597 : CollatzResearch.WordTrace tailWord_7414597 prefixEnd_7414597 3807252120384832088838395 := by
  unfold tailWord_7414597
  simp only [CollatzResearch.WordTrace]
  refine ⟨270432569519188856196434045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180288379679459237464289363 270432569519188856196434045)
  ·
    refine ⟨101412213569695821073662767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 270432569519188856196434045 101412213569695821073662767)
    ·
      refine ⟨152118320354543731610494151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101412213569695821073662767 152118320354543731610494151)
      ·
        refine ⟨228177480531815597415741227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152118320354543731610494151 228177480531815597415741227)
        ·
          refine ⟨342266220797723396123611841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 228177480531815597415741227 342266220797723396123611841)
          ·
            refine ⟨256699665598292547092708881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 342266220797723396123611841 256699665598292547092708881)
            ·
              refine ⟨192524749198719410319531661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 256699665598292547092708881 192524749198719410319531661)
              ·
                refine ⟨72196780949519778869824373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 192524749198719410319531661 72196780949519778869824373)
                ·
                  refine ⟨6768448214017479269046035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 72196780949519778869824373 6768448214017479269046035)
                  ·
                    refine ⟨10152672321026218903569053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6768448214017479269046035 10152672321026218903569053)
                    ·
                      refine ⟨3807252120384832088838395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10152672321026218903569053 3807252120384832088838395)
                      ·
                        rfl

theorem cell23_7414597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 3, 5, 1, 3].length) (baseStart_7414597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7414597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7414597 prefixEnd_7414597 := by exact prefixLift 7414597
  have htrace : WordTrace (prefixWord ++ tailWord_7414597) baseStart_7414597 baseEnd_7414597 := by
    simpa [prefixWord, tailWord_7414597, baseEnd_7414597] using wordTrace_append hprefix tailTrace_7414597
  have hstable : (prefixWord ++ tailWord_7414597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7414597).length < 2 ^ (prefixWord ++ tailWord_7414597).sum := by decide
  have hdescent : baseEnd_7414597 < baseStart_7414597 := by decide
  rcases family_descends (prefixWord ++ tailWord_7414597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7414607 : List Nat := [1, 1, 2, 1, 1, 2, 1, 1, 8, 3, 2]
def baseStart_7414607 : Nat := 118140960795 + 7414607 * 2 ^ 59
def prefixEnd_7414607 : Nat := 4983230072969 + 3 ^ 40 * 7414607 * 2
def baseEnd_7414607 : Nat := 3807257255191377049713349

theorem tailTrace_7414607 : CollatzResearch.WordTrace tailWord_7414607 prefixEnd_7414607 3807257255191377049713349 := by
  unfold tailWord_7414607
  simp only [CollatzResearch.WordTrace]
  refine ⟨270432934249152627904298075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180288622832768418602865383 270432934249152627904298075)
  ·
    refine ⟨405649401373728941856447113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270432934249152627904298075 405649401373728941856447113)
    ·
      refine ⟨304237051030296706392335335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 405649401373728941856447113 304237051030296706392335335)
      ·
        refine ⟨456355576545445059588503003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 304237051030296706392335335 456355576545445059588503003)
        ·
          refine ⟨684533364818167589382754505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 456355576545445059588503003 684533364818167589382754505)
          ·
            refine ⟨513400023613625692037065879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 684533364818167589382754505 513400023613625692037065879)
            ·
              refine ⟨770100035420438538055598819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 513400023613625692037065879 770100035420438538055598819)
              ·
                refine ⟨1155150053130657807083398229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 770100035420438538055598819 1155150053130657807083398229)
                ·
                  refine ⟨13536914685124896176758573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 1155150053130657807083398229 13536914685124896176758573)
                  ·
                    refine ⟨5076343006921836066284465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13536914685124896176758573 5076343006921836066284465)
                    ·
                      refine ⟨3807257255191377049713349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5076343006921836066284465 3807257255191377049713349)
                      ·
                        rfl

theorem cell23_7414607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 1, 8, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 1, 8, 3, 2].length) (baseStart_7414607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7414607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7414607 prefixEnd_7414607 := by exact prefixLift 7414607
  have htrace : WordTrace (prefixWord ++ tailWord_7414607) baseStart_7414607 baseEnd_7414607 := by
    simpa [prefixWord, tailWord_7414607, baseEnd_7414607] using wordTrace_append hprefix tailTrace_7414607
  have hstable : (prefixWord ++ tailWord_7414607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7414607).length < 2 ^ (prefixWord ++ tailWord_7414607).sum := by decide
  have hdescent : baseEnd_7414607 < baseStart_7414607 := by decide
  rcases family_descends (prefixWord ++ tailWord_7414607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7414617 : List Nat := [1, 2, 1, 2, 2, 4, 2, 3, 1, 5]
def baseStart_7414617 : Nat := 118140960795 + 7414617 * 2 ^ 59
def prefixEnd_7414617 : Nat := 4983230072969 + 3 ^ 40 * 7414617 * 2
def baseEnd_7414617 : Nat := 1269087463332640670196101

theorem tailTrace_7414617 : CollatzResearch.WordTrace tailWord_7414617 prefixEnd_7414617 1269087463332640670196101 := by
  unfold tailWord_7414617
  simp only [CollatzResearch.WordTrace]
  refine ⟨270433298979116399612162105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180288865986077599741441403 270433298979116399612162105)
  ·
    refine ⟨202824974234337299709121579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 270433298979116399612162105 202824974234337299709121579)
    ·
      refine ⟨304237461351505949563682369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202824974234337299709121579 304237461351505949563682369)
      ·
        refine ⟨228178096013629462172761777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 304237461351505949563682369 228178096013629462172761777)
        ·
          refine ⟨171133572010222096629571333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 228178096013629462172761777 171133572010222096629571333)
          ·
            refine ⟨32087544751916643118044625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 171133572010222096629571333 32087544751916643118044625)
            ·
              refine ⟨24065658563937482338533469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32087544751916643118044625 24065658563937482338533469)
              ·
                refine ⟨9024621961476555876950051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24065658563937482338533469 9024621961476555876950051)
                ·
                  refine ⟨13536932942214833815425077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9024621961476555876950051 13536932942214833815425077)
                  ·
                    refine ⟨1269087463332640670196101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13536932942214833815425077 1269087463332640670196101)
                    ·
                      rfl

theorem cell23_7414617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 2, 3, 1, 5].length) (baseStart_7414617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7414617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7414617 prefixEnd_7414617 := by exact prefixLift 7414617
  have htrace : WordTrace (prefixWord ++ tailWord_7414617) baseStart_7414617 baseEnd_7414617 := by
    simpa [prefixWord, tailWord_7414617, baseEnd_7414617] using wordTrace_append hprefix tailTrace_7414617
  have hstable : (prefixWord ++ tailWord_7414617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7414617).length < 2 ^ (prefixWord ++ tailWord_7414617).sum := by decide
  have hdescent : baseEnd_7414617 < baseStart_7414617 := by decide
  rcases family_descends (prefixWord ++ tailWord_7414617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7414624 : List Nat := [2, 1, 1, 3, 3, 1, 3, 2, 2, 3, 2]
def baseStart_7414624 : Nat := 118140960795 + 7414624 * 2 ^ 59
def prefixEnd_7414624 : Nat := 4983230072969 + 3 ^ 40 * 7414624 * 2
def baseEnd_7414624 : Nat := 3807265984362503483200771

theorem tailTrace_7414624 : CollatzResearch.WordTrace tailWord_7414624 prefixEnd_7414624 3807265984362503483200771 := by
  unfold tailWord_7414624
  simp only [CollatzResearch.WordTrace]
  refine ⟨135216777145045519903833463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180289036193394026538444617 135216777145045519903833463)
  ·
    refine ⟨202825165717568279855750195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135216777145045519903833463 202825165717568279855750195)
    ·
      refine ⟨304237748576352419783625293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202825165717568279855750195 304237748576352419783625293)
      ·
        refine ⟨114089155716132157418859485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 304237748576352419783625293 114089155716132157418859485)
        ·
          refine ⟨42783433393549559032072307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 114089155716132157418859485 42783433393549559032072307)
          ·
            refine ⟨64175150090324338548108461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42783433393549559032072307 64175150090324338548108461)
            ·
              refine ⟨24065681283871626955540673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64175150090324338548108461 24065681283871626955540673)
              ·
                refine ⟨18049260962903720216655505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24065681283871626955540673 18049260962903720216655505)
                ·
                  refine ⟨13536945722177790162491629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18049260962903720216655505 13536945722177790162491629)
                  ·
                    refine ⟨5076354645816671310934361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13536945722177790162491629 5076354645816671310934361)
                    ·
                      refine ⟨3807265984362503483200771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5076354645816671310934361 3807265984362503483200771)
                      ·
                        rfl

theorem cell23_7414624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 3, 2, 2, 3, 2].length) (baseStart_7414624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7414624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7414624 prefixEnd_7414624 := by exact prefixLift 7414624
  have htrace : WordTrace (prefixWord ++ tailWord_7414624) baseStart_7414624 baseEnd_7414624 := by
    simpa [prefixWord, tailWord_7414624, baseEnd_7414624] using wordTrace_append hprefix tailTrace_7414624
  have hstable : (prefixWord ++ tailWord_7414624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7414624).length < 2 ^ (prefixWord ++ tailWord_7414624).sum := by decide
  have hdescent : baseEnd_7414624 < baseStart_7414624 := by decide
  rcases family_descends (prefixWord ++ tailWord_7414624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7414631 : List Nat := [1, 1, 5, 1, 2, 4, 1, 1, 3, 1, 3]
def baseStart_7414631 : Nat := 118140960795 + 7414631 * 2 ^ 59
def prefixEnd_7414631 : Nat := 4983230072969 + 3 ^ 40 * 7414631 * 2
def baseEnd_7414631 : Nat := 3807269578727084955813239

theorem tailTrace_7414631 : CollatzResearch.WordTrace tailWord_7414631 prefixEnd_7414631 3807269578727084955813239 := by
  unfold tailWord_7414631
  simp only [CollatzResearch.WordTrace]
  refine ⟨270433809601065680003171747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180289206400710453335447831 270433809601065680003171747)
  ·
    refine ⟨405650714401598520004757621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270433809601065680003171747 405650714401598520004757621)
    ·
      refine ⟨38029754475149861250446027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 405650714401598520004757621 38029754475149861250446027)
      ·
        refine ⟨57044631712724791875669041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38029754475149861250446027 57044631712724791875669041)
        ·
          refine ⟨42783473784543593906751781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57044631712724791875669041 42783473784543593906751781)
          ·
            refine ⟨8021901334601923857515959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42783473784543593906751781 8021901334601923857515959)
            ·
              refine ⟨12032852001902885786273939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8021901334601923857515959 12032852001902885786273939)
              ·
                refine ⟨18049278002854328679410909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12032852001902885786273939 18049278002854328679410909)
                ·
                  refine ⟨6768479251070373254779091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18049278002854328679410909 6768479251070373254779091)
                  ·
                    refine ⟨10152718876605559882168637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6768479251070373254779091 10152718876605559882168637)
                    ·
                      refine ⟨3807269578727084955813239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10152718876605559882168637 3807269578727084955813239)
                      ·
                        rfl

theorem cell23_7414631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 4, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 4, 1, 1, 3, 1, 3].length) (baseStart_7414631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7414631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7414631 prefixEnd_7414631 := by exact prefixLift 7414631
  have htrace : WordTrace (prefixWord ++ tailWord_7414631) baseStart_7414631 baseEnd_7414631 := by
    simpa [prefixWord, tailWord_7414631, baseEnd_7414631] using wordTrace_append hprefix tailTrace_7414631
  have hstable : (prefixWord ++ tailWord_7414631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7414631).length < 2 ^ (prefixWord ++ tailWord_7414631).sum := by decide
  have hdescent : baseEnd_7414631 < baseStart_7414631 := by decide
  rcases family_descends (prefixWord ++ tailWord_7414631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7414637 : List Nat := [1, 5, 1, 1, 1, 1, 1, 4, 3, 1, 4]
def baseStart_7414637 : Nat := 118140960795 + 7414637 * 2 ^ 59
def prefixEnd_7414637 : Nat := 4983230072969 + 3 ^ 40 * 7414637 * 2
def baseEnd_7414637 : Nat := 3807272659611011932338211

theorem tailTrace_7414637 : CollatzResearch.WordTrace tailWord_7414637 prefixEnd_7414637 3807272659611011932338211 := by
  unfold tailWord_7414637
  simp only [CollatzResearch.WordTrace]
  refine ⟨270434028439043943027890165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180289352292695962018593443 270434028439043943027890165)
  ·
    refine ⟨25353190166160369658864703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 270434028439043943027890165 25353190166160369658864703)
    ·
      refine ⟨38029785249240554488297055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25353190166160369658864703 38029785249240554488297055)
      ·
        refine ⟨57044677873860831732445583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38029785249240554488297055 57044677873860831732445583)
        ·
          refine ⟨85567016810791247598668375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57044677873860831732445583 85567016810791247598668375)
          ·
            refine ⟨128350525216186871398002563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85567016810791247598668375 128350525216186871398002563)
            ·
              refine ⟨192525787824280307097003845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 128350525216186871398002563 192525787824280307097003845)
              ·
                refine ⟨36098585217052557580688221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 192525787824280307097003845 36098585217052557580688221)
                ·
                  refine ⟨13536969456394709092758083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36098585217052557580688221 13536969456394709092758083)
                  ·
                    refine ⟨20305454184592063639137125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13536969456394709092758083 20305454184592063639137125)
                    ·
                      refine ⟨3807272659611011932338211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20305454184592063639137125 3807272659611011932338211)
                      ·
                        rfl

theorem cell23_7414637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 4, 3, 1, 4].length) (baseStart_7414637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7414637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7414637 prefixEnd_7414637 := by exact prefixLift 7414637
  have htrace : WordTrace (prefixWord ++ tailWord_7414637) baseStart_7414637 baseEnd_7414637 := by
    simpa [prefixWord, tailWord_7414637, baseEnd_7414637] using wordTrace_append hprefix tailTrace_7414637
  have hstable : (prefixWord ++ tailWord_7414637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7414637).length < 2 ^ (prefixWord ++ tailWord_7414637).sum := by decide
  have hdescent : baseEnd_7414637 < baseStart_7414637 := by decide
  rcases family_descends (prefixWord ++ tailWord_7414637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7414638 : List Nat := [4, 1, 2, 3, 3, 1, 2, 1, 6]
def baseStart_7414638 : Nat := 118140960795 + 7414638 * 2 ^ 59
def prefixEnd_7414638 : Nat := 4983230072969 + 3 ^ 40 * 7414638 * 2
def baseEnd_7414638 : Nat := 423030352565740714269523

theorem tailTrace_7414638 : CollatzResearch.WordTrace tailWord_7414638 prefixEnd_7414638 423030352565740714269523 := by
  unfold tailWord_7414638
  simp only [CollatzResearch.WordTrace]
  refine ⟨33804258114005040024834571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 180289376608026880132451045 33804258114005040024834571)
  ·
    refine ⟨50706387171007560037251857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33804258114005040024834571 50706387171007560037251857)
    ·
      refine ⟨38029790378255670027938893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50706387171007560037251857 38029790378255670027938893)
      ·
        refine ⟨14261171391845876260477085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38029790378255670027938893 14261171391845876260477085)
        ·
          refine ⟨5347939271942203597678907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14261171391845876260477085 5347939271942203597678907)
          ·
            refine ⟨8021908907913305396518361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5347939271942203597678907 8021908907913305396518361)
            ·
              refine ⟨6016431680934979047388771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8021908907913305396518361 6016431680934979047388771)
              ·
                refine ⟨9024647521402468571083157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6016431680934979047388771 9024647521402468571083157)
                ·
                  refine ⟨423030352565740714269523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9024647521402468571083157 423030352565740714269523)
                  ·
                    rfl

theorem cell23_7414638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 3, 1, 2, 1, 6].length) (baseStart_7414638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7414638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7414638 prefixEnd_7414638 := by exact prefixLift 7414638
  have htrace : WordTrace (prefixWord ++ tailWord_7414638) baseStart_7414638 baseEnd_7414638 := by
    simpa [prefixWord, tailWord_7414638, baseEnd_7414638] using wordTrace_append hprefix tailTrace_7414638
  have hstable : (prefixWord ++ tailWord_7414638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7414638).length < 2 ^ (prefixWord ++ tailWord_7414638).sum := by decide
  have hdescent : baseEnd_7414638 < baseStart_7414638 := by decide
  rcases family_descends (prefixWord ++ tailWord_7414638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7414682 : List Nat := [3, 1, 1, 4, 4, 1, 2, 2, 1, 1, 3]
def baseStart_7414682 : Nat := 118140960795 + 7414682 * 2 ^ 59
def prefixEnd_7414682 : Nat := 4983230072969 + 3 ^ 40 * 7414682 * 2
def baseEnd_7414682 : Nat := 3807295766240464256275505

theorem tailTrace_7414682 : CollatzResearch.WordTrace tailWord_7414682 prefixEnd_7414682 3807295766240464256275505 := by
  unfold tailWord_7414682
  simp only [CollatzResearch.WordTrace]
  refine ⟨67608917430970228928319575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 180290446482587277142185533 67608917430970228928319575)
  ·
    refine ⟨101413376146455343392479363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67608917430970228928319575 101413376146455343392479363)
    ·
      refine ⟨152120064219683015088719045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101413376146455343392479363 152120064219683015088719045)
      ·
        refine ⟨28522512041190565329134821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 152120064219683015088719045 28522512041190565329134821)
        ·
          refine ⟨5347971007723230999212779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28522512041190565329134821 5347971007723230999212779)
          ·
            refine ⟨8021956511584846498819169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5347971007723230999212779 8021956511584846498819169)
            ·
              refine ⟨6016467383688634874114377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8021956511584846498819169 6016467383688634874114377)
              ·
                refine ⟨4512350537766476155585783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6016467383688634874114377 4512350537766476155585783)
                ·
                  refine ⟨6768525806649714233378675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4512350537766476155585783 6768525806649714233378675)
                  ·
                    refine ⟨10152788709974571350068013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6768525806649714233378675 10152788709974571350068013)
                    ·
                      refine ⟨3807295766240464256275505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10152788709974571350068013 3807295766240464256275505)
                      ·
                        rfl

theorem cell23_7414682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 4, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 4, 1, 2, 2, 1, 1, 3].length) (baseStart_7414682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7414682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7414682 prefixEnd_7414682 := by exact prefixLift 7414682
  have htrace : WordTrace (prefixWord ++ tailWord_7414682) baseStart_7414682 baseEnd_7414682 := by
    simpa [prefixWord, tailWord_7414682, baseEnd_7414682] using wordTrace_append hprefix tailTrace_7414682
  have hstable : (prefixWord ++ tailWord_7414682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7414682).length < 2 ^ (prefixWord ++ tailWord_7414682).sum := by decide
  have hdescent : baseEnd_7414682 < baseStart_7414682 := by decide
  rcases family_descends (prefixWord ++ tailWord_7414682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7414714 : List Nat := [3, 1, 1, 1, 2, 1, 3, 3, 3, 3, 2]
def baseStart_7414714 : Nat := 118140960795 + 7414714 * 2 ^ 59
def prefixEnd_7414714 : Nat := 4983230072969 + 3 ^ 40 * 7414714 * 2
def baseEnd_7414714 : Nat := 3807312197621408131075357

theorem tailTrace_7414714 : CollatzResearch.WordTrace tailWord_7414714 prefixEnd_7414714 3807312197621408131075357 := by
  unfold tailWord_7414714
  simp only [CollatzResearch.WordTrace]
  refine ⟨67609209214941246294610799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 180291224573176656785628797 67609209214941246294610799)
  ·
    refine ⟨101413813822411869441916199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67609209214941246294610799 101413813822411869441916199)
    ·
      refine ⟨152120720733617804162874299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101413813822411869441916199 152120720733617804162874299)
      ·
        refine ⟨228181081100426706244311449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152120720733617804162874299 228181081100426706244311449)
        ·
          refine ⟨171135810825320029683233587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 228181081100426706244311449 171135810825320029683233587)
          ·
            refine ⟨256703716237980044524850381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 171135810825320029683233587 256703716237980044524850381)
            ·
              refine ⟨96263893589242516696818893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 256703716237980044524850381 96263893589242516696818893)
              ·
                refine ⟨36098960095965943761307085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 96263893589242516696818893 36098960095965943761307085)
                ·
                  refine ⟨13537110035987228910490157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36098960095965943761307085 13537110035987228910490157)
                  ·
                    refine ⟨5076416263495210841433809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13537110035987228910490157 5076416263495210841433809)
                    ·
                      refine ⟨3807312197621408131075357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5076416263495210841433809 3807312197621408131075357)
                      ·
                        rfl

theorem cell23_7414714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 3, 3, 3, 2].length) (baseStart_7414714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7414714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7414714 prefixEnd_7414714 := by exact prefixLift 7414714
  have htrace : WordTrace (prefixWord ++ tailWord_7414714) baseStart_7414714 baseEnd_7414714 := by
    simpa [prefixWord, tailWord_7414714, baseEnd_7414714] using wordTrace_append hprefix tailTrace_7414714
  have hstable : (prefixWord ++ tailWord_7414714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7414714).length < 2 ^ (prefixWord ++ tailWord_7414714).sum := by decide
  have hdescent : baseEnd_7414714 < baseStart_7414714 := by decide
  rcases family_descends (prefixWord ++ tailWord_7414714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7414731 : List Nat := [1, 1, 1, 1, 3, 6, 1, 3, 1, 3, 2]
def baseStart_7414731 : Nat := 118140960795 + 7414731 * 2 ^ 59
def prefixEnd_7414731 : Nat := 4983230072969 + 3 ^ 40 * 7414731 * 2
def baseEnd_7414731 : Nat := 3807320926792534564562779

theorem tailTrace_7414731 : CollatzResearch.WordTrace tailWord_7414731 prefixEnd_7414731 3807320926792534564562779 := by
  unfold tailWord_7414731
  simp only [CollatzResearch.WordTrace]
  refine ⟨270437456900703397081812047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180291637933802264721208031 270437456900703397081812047)
  ·
    refine ⟨405656185351055095622718071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270437456900703397081812047 405656185351055095622718071)
    ·
      refine ⟨608484278026582643434077107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 405656185351055095622718071 608484278026582643434077107)
      ·
        refine ⟨912726417039873965151115661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 608484278026582643434077107 912726417039873965151115661)
        ·
          refine ⟨342272406389952736931668373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 912726417039873965151115661 342272406389952736931668373)
          ·
            refine ⟨16044019049529034543671955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 342272406389952736931668373 16044019049529034543671955)
            ·
              refine ⟨24066028574293551815507933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16044019049529034543671955 24066028574293551815507933)
              ·
                refine ⟨9024760715360081930815475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24066028574293551815507933 9024760715360081930815475)
                ·
                  refine ⟨13537141073040122896223213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9024760715360081930815475 13537141073040122896223213)
                  ·
                    refine ⟨5076427902390046086083705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13537141073040122896223213 5076427902390046086083705)
                    ·
                      refine ⟨3807320926792534564562779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5076427902390046086083705 3807320926792534564562779)
                      ·
                        rfl

theorem cell23_7414731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 1, 3, 1, 3, 2].length) (baseStart_7414731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7414731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7414731 prefixEnd_7414731 := by exact prefixLift 7414731
  have htrace : WordTrace (prefixWord ++ tailWord_7414731) baseStart_7414731 baseEnd_7414731 := by
    simpa [prefixWord, tailWord_7414731, baseEnd_7414731] using wordTrace_append hprefix tailTrace_7414731
  have hstable : (prefixWord ++ tailWord_7414731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7414731).length < 2 ^ (prefixWord ++ tailWord_7414731).sum := by decide
  have hdescent : baseEnd_7414731 < baseStart_7414731 := by decide
  rcases family_descends (prefixWord ++ tailWord_7414731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7414738 : List Nat := [3, 2, 2, 3, 1, 1, 3, 2, 2, 1, 3]
def baseStart_7414738 : Nat := 118140960795 + 7414738 * 2 ^ 59
def prefixEnd_7414738 : Nat := 4983230072969 + 3 ^ 40 * 7414738 * 2
def baseEnd_7414738 : Nat := 3807324521157116037175247

theorem tailTrace_7414738 : CollatzResearch.WordTrace tailWord_7414738 prefixEnd_7414738 3807324521157116037175247 := by
  unfold tailWord_7414738
  simp only [CollatzResearch.WordTrace]
  refine ⟨67609428052919509319329217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 180291808141118691518211245 67609428052919509319329217)
  ·
    refine ⟨50707071039689631989496913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67609428052919509319329217 50707071039689631989496913)
    ·
      refine ⟨38030303279767223992122685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50707071039689631989496913 38030303279767223992122685)
      ·
        refine ⟨14261363729912708997046007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38030303279767223992122685 14261363729912708997046007)
        ·
          refine ⟨21392045594869063495569011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14261363729912708997046007 21392045594869063495569011)
          ·
            refine ⟨32088068392303595243353517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21392045594869063495569011 32088068392303595243353517)
            ·
              refine ⟨12033025647113848216257569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32088068392303595243353517 12033025647113848216257569)
              ·
                refine ⟨9024769235335386162193177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12033025647113848216257569 9024769235335386162193177)
                ·
                  refine ⟨6768576926501539621644883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9024769235335386162193177 6768576926501539621644883)
                  ·
                    refine ⟨10152865389752309432467325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6768576926501539621644883 10152865389752309432467325)
                    ·
                      refine ⟨3807324521157116037175247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10152865389752309432467325 3807324521157116037175247)
                      ·
                        rfl

theorem cell23_7414738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 3, 2, 2, 1, 3].length) (baseStart_7414738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7414738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7414738 prefixEnd_7414738 := by exact prefixLift 7414738
  have htrace : WordTrace (prefixWord ++ tailWord_7414738) baseStart_7414738 baseEnd_7414738 := by
    simpa [prefixWord, tailWord_7414738, baseEnd_7414738] using wordTrace_append hprefix tailTrace_7414738
  have hstable : (prefixWord ++ tailWord_7414738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7414738).length < 2 ^ (prefixWord ++ tailWord_7414738).sum := by decide
  have hdescent : baseEnd_7414738 < baseStart_7414738 := by decide
  rcases family_descends (prefixWord ++ tailWord_7414738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7414767 : List Nat := [1, 1, 2, 1, 4, 3, 2, 2, 7]
def baseStart_7414767 : Nat := 118140960795 + 7414767 * 2 ^ 59
def prefixEnd_7414767 : Nat := 4983230072969 + 3 ^ 40 * 7414767 * 2
def baseEnd_7414767 : Nat := 423037712455121824856957

theorem tailTrace_7414767 : CollatzResearch.WordTrace tailWord_7414767 prefixEnd_7414767 423037712455121824856957 := by
  unfold tailWord_7414767
  simp only [CollatzResearch.WordTrace]
  refine ⟨270438769928572975230122555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180292513285715316820081703 270438769928572975230122555)
  ·
    refine ⟨405658154892859462845183833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270438769928572975230122555 405658154892859462845183833)
    ·
      refine ⟨304243616169644597133887875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 405658154892859462845183833 304243616169644597133887875)
      ·
        refine ⟨456365424254466895700831813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 304243616169644597133887875 456365424254466895700831813)
        ·
          refine ⟨85568517047712542943905965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 456365424254466895700831813 85568517047712542943905965)
          ·
            refine ⟨32088193892892203603964737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 85568517047712542943905965 32088193892892203603964737)
            ·
              refine ⟨24066145419669152702973553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32088193892892203603964737 24066145419669152702973553)
              ·
                refine ⟨18049609064751864527230165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24066145419669152702973553 18049609064751864527230165)
                ·
                  refine ⟨423037712455121824856957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18049609064751864527230165 423037712455121824856957)
                  ·
                    rfl

theorem cell23_7414767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 2, 2, 7].length) (baseStart_7414767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7414767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7414767 prefixEnd_7414767 := by exact prefixLift 7414767
  have htrace : WordTrace (prefixWord ++ tailWord_7414767) baseStart_7414767 baseEnd_7414767 := by
    simpa [prefixWord, tailWord_7414767, baseEnd_7414767] using wordTrace_append hprefix tailTrace_7414767
  have hstable : (prefixWord ++ tailWord_7414767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7414767).length < 2 ^ (prefixWord ++ tailWord_7414767).sum := by decide
  have hdescent : baseEnd_7414767 < baseStart_7414767 := by decide
  rcases family_descends (prefixWord ++ tailWord_7414767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7414812 : List Nat := [2, 2, 3, 1, 4, 2, 2, 1, 2, 2, 2]
def baseStart_7414812 : Nat := 118140960795 + 7414812 * 2 ^ 59
def prefixEnd_7414812 : Nat := 4983230072969 + 3 ^ 40 * 7414812 * 2
def baseEnd_7414812 : Nat := 3807362518725548747649907

theorem tailTrace_7414812 : CollatzResearch.WordTrace tailWord_7414812 prefixEnd_7414812 3807362518725548747649907 := by
  unfold tailWord_7414812
  simp only [CollatzResearch.WordTrace]
  refine ⟨135220205606704973957755345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180293607475606631943673793 135220205606704973957755345)
  ·
    refine ⟨101415154205028730468316509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135220205606704973957755345 101415154205028730468316509)
    ·
      refine ⟨38030682826885773925618691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 101415154205028730468316509 38030682826885773925618691)
      ·
        refine ⟨57046024240328660888428037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38030682826885773925618691 57046024240328660888428037)
        ·
          refine ⟨10696129545061623916580257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 57046024240328660888428037 10696129545061623916580257)
          ·
            refine ⟨8022097158796217937435193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10696129545061623916580257 8022097158796217937435193)
            ·
              refine ⟨6016572869097163453076395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8022097158796217937435193 6016572869097163453076395)
              ·
                refine ⟨9024859303645745179614593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6016572869097163453076395 9024859303645745179614593)
                ·
                  refine ⟨6768644477734308884710945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9024859303645745179614593 6768644477734308884710945)
                  ·
                    refine ⟨5076483358300731663533209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6768644477734308884710945 5076483358300731663533209)
                    ·
                      refine ⟨3807362518725548747649907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5076483358300731663533209 3807362518725548747649907)
                      ·
                        rfl

theorem cell23_7414812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 2, 2, 1, 2, 2, 2].length) (baseStart_7414812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7414812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7414812 prefixEnd_7414812 := by exact prefixLift 7414812
  have htrace : WordTrace (prefixWord ++ tailWord_7414812) baseStart_7414812 baseEnd_7414812 := by
    simpa [prefixWord, tailWord_7414812, baseEnd_7414812] using wordTrace_append hprefix tailTrace_7414812
  have hstable : (prefixWord ++ tailWord_7414812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7414812).length < 2 ^ (prefixWord ++ tailWord_7414812).sum := by decide
  have hdescent : baseEnd_7414812 < baseStart_7414812 := by decide
  rcases family_descends (prefixWord ++ tailWord_7414812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7414847 : List Nat := [1, 1, 2, 2, 3, 1, 1, 3, 2, 1, 6]
def baseStart_7414847 : Nat := 118140960795 + 7414847 * 2 ^ 59
def prefixEnd_7414847 : Nat := 4983230072969 + 3 ^ 40 * 7414847 * 2
def baseEnd_7414847 : Nat := 3807380490548456110712245

theorem tailTrace_7414847 : CollatzResearch.WordTrace tailWord_7414847 prefixEnd_7414847 3807380490548456110712245 := by
  unfold tailWord_7414847
  simp only [CollatzResearch.WordTrace]
  refine ⟨270441687768283148893034795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180294458512188765928689863 270441687768283148893034795)
  ·
    refine ⟨405662531652424723339552193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270441687768283148893034795 405662531652424723339552193)
    ·
      refine ⟨304246898739318542504664145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 405662531652424723339552193 304246898739318542504664145)
      ·
        refine ⟨228185174054488906878498109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 304246898739318542504664145 228185174054488906878498109)
        ·
          refine ⟨85569440270433340079436791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 228185174054488906878498109 85569440270433340079436791)
          ·
            refine ⟨128354160405650010119155187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85569440270433340079436791 128354160405650010119155187)
            ·
              refine ⟨192531240608475015178732781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 128354160405650010119155187 192531240608475015178732781)
              ·
                refine ⟨72199215228178130692024793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 192531240608475015178732781 72199215228178130692024793)
                ·
                  refine ⟨54149411421133598019018595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 72199215228178130692024793 54149411421133598019018595)
                  ·
                    refine ⟨81224117131700397028527893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 54149411421133598019018595 81224117131700397028527893)
                    ·
                      refine ⟨3807380490548456110712245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 81224117131700397028527893 3807380490548456110712245)
                      ·
                        rfl

theorem cell23_7414847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 3, 2, 1, 6].length) (baseStart_7414847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7414847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7414847 prefixEnd_7414847 := by exact prefixLift 7414847
  have htrace : WordTrace (prefixWord ++ tailWord_7414847) baseStart_7414847 baseEnd_7414847 := by
    simpa [prefixWord, tailWord_7414847, baseEnd_7414847] using wordTrace_append hprefix tailTrace_7414847
  have hstable : (prefixWord ++ tailWord_7414847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7414847).length < 2 ^ (prefixWord ++ tailWord_7414847).sum := by decide
  have hdescent : baseEnd_7414847 < baseStart_7414847 := by decide
  rcases family_descends (prefixWord ++ tailWord_7414847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7414888 : List Nat := [2, 1, 4, 4, 1, 1, 1, 1, 1, 4, 3]
def baseStart_7414888 : Nat := 118140960795 + 7414888 * 2 ^ 59
def prefixEnd_7414888 : Nat := 4983230072969 + 3 ^ 40 * 7414888 * 2
def baseEnd_7414888 : Nat := 3807401543255290450299557

theorem tailTrace_7414888 : CollatzResearch.WordTrace tailWord_7414888 prefixEnd_7414888 3807401543255290450299557 := by
  unfold tailWord_7414888
  simp only [CollatzResearch.WordTrace]
  refine ⟨135221591580567306447638659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180295455440756408596851545 135221591580567306447638659)
  ·
    refine ⟨202832387370850959671457989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135221591580567306447638659 202832387370850959671457989)
    ·
      refine ⟨38031072632034554938398373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 202832387370850959671457989 38031072632034554938398373)
      ·
        refine ⟨7130826118506479050949695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38031072632034554938398373 7130826118506479050949695)
        ·
          refine ⟨10696239177759718576424543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7130826118506479050949695 10696239177759718576424543)
          ·
            refine ⟨16044358766639577864636815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10696239177759718576424543 16044358766639577864636815)
            ·
              refine ⟨24066538149959366796955223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16044358766639577864636815 24066538149959366796955223)
              ·
                refine ⟨36099807224939050195432835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24066538149959366796955223 36099807224939050195432835)
                ·
                  refine ⟨54149710837408575293149253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36099807224939050195432835 54149710837408575293149253)
                  ·
                    refine ⟨10153070782014107867465485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 54149710837408575293149253 10153070782014107867465485)
                    ·
                      refine ⟨3807401543255290450299557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10153070782014107867465485 3807401543255290450299557)
                      ·
                        rfl

theorem cell23_7414888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 1, 1, 1, 4, 3].length) (baseStart_7414888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7414888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7414888 prefixEnd_7414888 := by exact prefixLift 7414888
  have htrace : WordTrace (prefixWord ++ tailWord_7414888) baseStart_7414888 baseEnd_7414888 := by
    simpa [prefixWord, tailWord_7414888, baseEnd_7414888] using wordTrace_append hprefix tailTrace_7414888
  have hstable : (prefixWord ++ tailWord_7414888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7414888).length < 2 ^ (prefixWord ++ tailWord_7414888).sum := by decide
  have hdescent : baseEnd_7414888 < baseStart_7414888 := by decide
  rcases family_descends (prefixWord ++ tailWord_7414888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7414924 : List Nat := [2, 2, 1, 2, 1, 1, 1, 3, 5, 1, 4]
def baseStart_7414924 : Nat := 118140960795 + 7414924 * 2 ^ 59
def prefixEnd_7414924 : Nat := 4983230072969 + 3 ^ 40 * 7414924 * 2
def baseEnd_7414924 : Nat := 3807420028558852309449391

theorem tailTrace_7414924 : CollatzResearch.WordTrace tailWord_7414924 prefixEnd_7414924 3807420028558852309449391 := by
  unfold tailWord_7414924
  simp only [CollatzResearch.WordTrace]
  refine ⟨135222248094502095521793913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180296330792669460695725217 135222248094502095521793913)
  ·
    refine ⟨101416686070876571641345435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135222248094502095521793913 101416686070876571641345435)
    ·
      refine ⟨152125029106314857462018153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101416686070876571641345435 152125029106314857462018153)
      ·
        refine ⟨114093771829736143096513615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 152125029106314857462018153 114093771829736143096513615)
        ·
          refine ⟨171140657744604214644770423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114093771829736143096513615 171140657744604214644770423)
          ·
            refine ⟨256710986616906321967155635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 171140657744604214644770423 256710986616906321967155635)
            ·
              refine ⟨385066479925359482950733453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 256710986616906321967155635 385066479925359482950733453)
              ·
                refine ⟨144399929972009806106525045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 385066479925359482950733453 144399929972009806106525045)
                ·
                  refine ⟨13537493434875919322486723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 144399929972009806106525045 13537493434875919322486723)
                  ·
                    refine ⟨20306240152313878983730085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13537493434875919322486723 20306240152313878983730085)
                    ·
                      refine ⟨3807420028558852309449391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20306240152313878983730085 3807420028558852309449391)
                      ·
                        rfl

theorem cell23_7414924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 3, 5, 1, 4].length) (baseStart_7414924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7414924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7414924 prefixEnd_7414924 := by exact prefixLift 7414924
  have htrace : WordTrace (prefixWord ++ tailWord_7414924) baseStart_7414924 baseEnd_7414924 := by
    simpa [prefixWord, tailWord_7414924, baseEnd_7414924] using wordTrace_append hprefix tailTrace_7414924
  have hstable : (prefixWord ++ tailWord_7414924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7414924).length < 2 ^ (prefixWord ++ tailWord_7414924).sum := by decide
  have hdescent : baseEnd_7414924 < baseStart_7414924 := by decide
  rcases family_descends (prefixWord ++ tailWord_7414924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7414938 : List Nat := [3, 1, 1, 5, 1, 2, 2, 2, 1, 5]
def baseStart_7414938 : Nat := 118140960795 + 7414938 * 2 ^ 59
def prefixEnd_7414938 : Nat := 4983230072969 + 3 ^ 40 * 7414938 * 2
def baseEnd_7414938 : Nat := 1269142405762671751558109

theorem tailTrace_7414938 : CollatzResearch.WordTrace tailWord_7414938 prefixEnd_7414938 1269142405762671751558109 := by
  unfold tailWord_7414938
  simp only [CollatzResearch.WordTrace]
  refine ⟨67611251702738367858649367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 180296671207302314289731645 67611251702738367858649367)
  ·
    refine ⟨101416877554107551787974051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67611251702738367858649367 101416877554107551787974051)
    ·
      refine ⟨152125316331161327681961077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101416877554107551787974051 152125316331161327681961077)
      ·
        refine ⟨14261748406046374470183851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 152125316331161327681961077 14261748406046374470183851)
        ·
          refine ⟨21392622609069561705275777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14261748406046374470183851 21392622609069561705275777)
          ·
            refine ⟨16044466956802171278956833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21392622609069561705275777 16044466956802171278956833)
            ·
              refine ⟨12033350217601628459217625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16044466956802171278956833 12033350217601628459217625)
              ·
                refine ⟨9025012663201221344413219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12033350217601628459217625 9025012663201221344413219)
                ·
                  refine ⟨13537518994801832016619829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9025012663201221344413219 13537518994801832016619829)
                  ·
                    refine ⟨1269142405762671751558109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13537518994801832016619829 1269142405762671751558109)
                    ·
                      rfl

theorem cell23_7414938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 2, 2, 1, 5].length) (baseStart_7414938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7414938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7414938 prefixEnd_7414938 := by exact prefixLift 7414938
  have htrace : WordTrace (prefixWord ++ tailWord_7414938) baseStart_7414938 baseEnd_7414938 := by
    simpa [prefixWord, tailWord_7414938, baseEnd_7414938] using wordTrace_append hprefix tailTrace_7414938
  have hstable : (prefixWord ++ tailWord_7414938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7414938).length < 2 ^ (prefixWord ++ tailWord_7414938).sum := by decide
  have hdescent : baseEnd_7414938 < baseStart_7414938 := by decide
  rcases family_descends (prefixWord ++ tailWord_7414938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7414941 : List Nat := [1, 4, 2, 1, 1, 2, 1, 1, 2, 6, 2]
def baseStart_7414941 : Nat := 118140960795 + 7414941 * 2 ^ 59
def prefixEnd_7414941 : Nat := 4983230072969 + 3 ^ 40 * 7414941 * 2
def baseEnd_7414941 : Nat := 3807428757729978742936813

theorem tailTrace_7414941 : CollatzResearch.WordTrace tailWord_7414941 prefixEnd_7414941 3807428757729978742936813 := by
  unfold tailWord_7414941
  simp only [CollatzResearch.WordTrace]
  refine ⟨270445116229942602946956677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180296744153295068631304451 270445116229942602946956677)
  ·
    refine ⟨50708459293114238052554377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 270445116229942602946956677 50708459293114238052554377)
    ·
      refine ⟨38031344469835678539415783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50708459293114238052554377 38031344469835678539415783)
      ·
        refine ⟨57047016704753517809123675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38031344469835678539415783 57047016704753517809123675)
        ·
          refine ⟨85570525057130276713685513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57047016704753517809123675 85570525057130276713685513)
          ·
            refine ⟨64177893792847707535264135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85570525057130276713685513 64177893792847707535264135)
            ·
              refine ⟨96266840689271561302896203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64177893792847707535264135 96266840689271561302896203)
              ·
                refine ⟨144400261033907341954344305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 96266840689271561302896203 144400261033907341954344305)
                ·
                  refine ⟨108300195775430506465758229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 144400261033907341954344305 108300195775430506465758229)
                  ·
                    refine ⟨5076571676973304990582417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 108300195775430506465758229 5076571676973304990582417)
                    ·
                      refine ⟨3807428757729978742936813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5076571676973304990582417 3807428757729978742936813)
                      ·
                        rfl

theorem cell23_7414941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 1, 2, 6, 2].length) (baseStart_7414941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7414941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7414941 prefixEnd_7414941 := by exact prefixLift 7414941
  have htrace : WordTrace (prefixWord ++ tailWord_7414941) baseStart_7414941 baseEnd_7414941 := by
    simpa [prefixWord, tailWord_7414941, baseEnd_7414941] using wordTrace_append hprefix tailTrace_7414941
  have hstable : (prefixWord ++ tailWord_7414941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7414941).length < 2 ^ (prefixWord ++ tailWord_7414941).sum := by decide
  have hdescent : baseEnd_7414941 < baseStart_7414941 := by decide
  rcases family_descends (prefixWord ++ tailWord_7414941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7414944 : List Nat := [2, 1, 1, 4, 2, 1, 1, 2, 3, 1, 5]
def baseStart_7414944 : Nat := 118140960795 + 7414944 * 2 ^ 59
def prefixEnd_7414944 : Nat := 4983230072969 + 3 ^ 40 * 7414944 * 2
def baseEnd_7414944 : Nat := 3807430298171942231199299

theorem tailTrace_7414944 : CollatzResearch.WordTrace tailWord_7414944 prefixEnd_7414944 3807430298171942231199299 := by
  unfold tailWord_7414944
  simp only [CollatzResearch.WordTrace]
  refine ⟨135222612824465867229657943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180296817099287822972877257 135222612824465867229657943)
  ·
    refine ⟨202833919236698800844486915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135222612824465867229657943 202833919236698800844486915)
    ·
      refine ⟨304250878855048201266730373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202833919236698800844486915 304250878855048201266730373)
      ·
        refine ⟨57047039785321537737511945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 304250878855048201266730373 57047039785321537737511945)
        ·
          refine ⟨42785279838991153303133959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57047039785321537737511945 42785279838991153303133959)
          ·
            refine ⟨64177919758486729954700939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42785279838991153303133959 64177919758486729954700939)
            ·
              refine ⟨96266879637730094932051409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64177919758486729954700939 96266879637730094932051409)
              ·
                refine ⟨72200159728297571199038557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 96266879637730094932051409 72200159728297571199038557)
                ·
                  refine ⟨27075059898111589199639459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 72200159728297571199038557 27075059898111589199639459)
                  ·
                    refine ⟨40612589847167383799459189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27075059898111589199639459 40612589847167383799459189)
                    ·
                      refine ⟨3807430298171942231199299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40612589847167383799459189 3807430298171942231199299)
                      ·
                        rfl

theorem cell23_7414944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 2, 3, 1, 5].length) (baseStart_7414944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7414944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7414944 prefixEnd_7414944 := by exact prefixLift 7414944
  have htrace : WordTrace (prefixWord ++ tailWord_7414944) baseStart_7414944 baseEnd_7414944 := by
    simpa [prefixWord, tailWord_7414944, baseEnd_7414944] using wordTrace_append hprefix tailTrace_7414944
  have hstable : (prefixWord ++ tailWord_7414944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7414944).length < 2 ^ (prefixWord ++ tailWord_7414944).sum := by decide
  have hdescent : baseEnd_7414944 < baseStart_7414944 := by decide
  rcases family_descends (prefixWord ++ tailWord_7414944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7414961 : List Nat := [1, 2, 2, 5, 1, 1, 1, 3, 1, 1, 5]
def baseStart_7414961 : Nat := 118140960795 + 7414961 * 2 ^ 59
def prefixEnd_7414961 : Nat := 4983230072969 + 3 ^ 40 * 7414961 * 2
def baseEnd_7414961 : Nat := 3807439027343068664686721

theorem tailTrace_7414961 : CollatzResearch.WordTrace tailWord_7414961 prefixEnd_7414961 3807439027343068664686721 := by
  unfold tailWord_7414961
  simp only [CollatzResearch.WordTrace]
  refine ⟨270445845689870146362684737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180297230459913430908456491 270445845689870146362684737)
  ·
    refine ⟨202834384267402609772013553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 270445845689870146362684737 202834384267402609772013553)
    ·
      refine ⟨152125788200551957329010165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 202834384267402609772013553 152125788200551957329010165)
      ·
        refine ⟨14261792643801745999594703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 152125788200551957329010165 14261792643801745999594703)
        ·
          refine ⟨21392688965702618999392055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14261792643801745999594703 21392688965702618999392055)
          ·
            refine ⟨32089033448553928499088083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21392688965702618999392055 32089033448553928499088083)
            ·
              refine ⟨48133550172830892748632125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32089033448553928499088083 48133550172830892748632125)
              ·
                refine ⟨18050081314811584780737047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48133550172830892748632125 18050081314811584780737047)
                ·
                  refine ⟨27075121972217377171105571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18050081314811584780737047 27075121972217377171105571)
                  ·
                    refine ⟨40612682958326065756658357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27075121972217377171105571 40612682958326065756658357)
                    ·
                      refine ⟨3807439027343068664686721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40612682958326065756658357 3807439027343068664686721)
                      ·
                        rfl

theorem cell23_7414961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 1, 3, 1, 1, 5].length) (baseStart_7414961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7414961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7414961 prefixEnd_7414961 := by exact prefixLift 7414961
  have htrace : WordTrace (prefixWord ++ tailWord_7414961) baseStart_7414961 baseEnd_7414961 := by
    simpa [prefixWord, tailWord_7414961, baseEnd_7414961] using wordTrace_append hprefix tailTrace_7414961
  have hstable : (prefixWord ++ tailWord_7414961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7414961).length < 2 ^ (prefixWord ++ tailWord_7414961).sum := by decide
  have hdescent : baseEnd_7414961 < baseStart_7414961 := by decide
  rcases family_descends (prefixWord ++ tailWord_7414961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7414975 : List Nat := [1, 1, 2, 2, 2, 2, 2, 6, 1, 2, 2]
def baseStart_7414975 : Nat := 118140960795 + 7414975 * 2 ^ 59
def prefixEnd_7414975 : Nat := 4983230072969 + 3 ^ 40 * 7414975 * 2
def baseEnd_7414975 : Nat := 3807446216072231609911657

theorem tailTrace_7414975 : CollatzResearch.WordTrace tailWord_7414975 prefixEnd_7414975 3807446216072231609911657 := by
  unfold tailWord_7414975
  simp only [CollatzResearch.WordTrace]
  refine ⟨270446356311819426753694379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180297570874546284502462919 270446356311819426753694379)
  ·
    refine ⟨405669534467729140130541569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270446356311819426753694379 405669534467729140130541569)
    ·
      refine ⟨304252150850796855097906177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 405669534467729140130541569 304252150850796855097906177)
      ·
        refine ⟨228189113138097641323429633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 304252150850796855097906177 228189113138097641323429633)
        ·
          refine ⟨171141834853573230992572225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 228189113138097641323429633 171141834853573230992572225)
          ·
            refine ⟨128356376140179923244429169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 171141834853573230992572225 128356376140179923244429169)
            ·
              refine ⟨96267282105134942433321877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 128356376140179923244429169 96267282105134942433321877)
              ·
                refine ⟨4512528848678200426561963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 96267282105134942433321877 4512528848678200426561963)
                ·
                  refine ⟨6768793273017300639842945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4512528848678200426561963 6768793273017300639842945)
                  ·
                    refine ⟨5076594954762975479882209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6768793273017300639842945 5076594954762975479882209)
                    ·
                      refine ⟨3807446216072231609911657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5076594954762975479882209 3807446216072231609911657)
                      ·
                        rfl

theorem cell23_7414975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 6, 1, 2, 2].length) (baseStart_7414975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7414975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7414975 prefixEnd_7414975 := by exact prefixLift 7414975
  have htrace : WordTrace (prefixWord ++ tailWord_7414975) baseStart_7414975 baseEnd_7414975 := by
    simpa [prefixWord, tailWord_7414975, baseEnd_7414975] using wordTrace_append hprefix tailTrace_7414975
  have hstable : (prefixWord ++ tailWord_7414975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7414975).length < 2 ^ (prefixWord ++ tailWord_7414975).sum := by decide
  have hdescent : baseEnd_7414975 < baseStart_7414975 := by decide
  rcases family_descends (prefixWord ++ tailWord_7414975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7414989 : List Nat := [1, 6, 2, 2, 2, 1, 1, 2, 1, 5]
def baseStart_7414989 : Nat := 118140960795 + 7414989 * 2 ^ 59
def prefixEnd_7414989 : Nat := 4983230072969 + 3 ^ 40 * 7414989 * 2
def baseEnd_7414989 : Nat := 1269151134933798185045531

theorem tailTrace_7414989 : CollatzResearch.WordTrace tailWord_7414989 prefixEnd_7414989 1269151134933798185045531 := by
  unfold tailWord_7414989
  simp only [CollatzResearch.WordTrace]
  refine ⟨270446866933768707144704021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180297911289179138096469347 270446866933768707144704021)
  ·
    refine ⟨12677196887520408147408001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 270446866933768707144704021 12677196887520408147408001)
    ·
      refine ⟨9507897665640306110556001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12677196887520408147408001 9507897665640306110556001)
      ·
        refine ⟨7130923249230229582917001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9507897665640306110556001 7130923249230229582917001)
        ·
          refine ⟨5348192436922672187187751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7130923249230229582917001 5348192436922672187187751)
          ·
            refine ⟨8022288655384008280781627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5348192436922672187187751 8022288655384008280781627)
            ·
              refine ⟨12033432983076012421172441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8022288655384008280781627 12033432983076012421172441)
              ·
                refine ⟨9025074737307009315879331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12033432983076012421172441 9025074737307009315879331)
                ·
                  refine ⟨13537612105960513973818997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9025074737307009315879331 13537612105960513973818997)
                  ·
                    refine ⟨1269151134933798185045531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13537612105960513973818997 1269151134933798185045531)
                    ·
                      rfl

theorem cell23_7414989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 2, 1, 1, 2, 1, 5].length) (baseStart_7414989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7414989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7414989 prefixEnd_7414989 := by exact prefixLift 7414989
  have htrace : WordTrace (prefixWord ++ tailWord_7414989) baseStart_7414989 baseEnd_7414989 := by
    simpa [prefixWord, tailWord_7414989, baseEnd_7414989] using wordTrace_append hprefix tailTrace_7414989
  have hstable : (prefixWord ++ tailWord_7414989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7414989).length < 2 ^ (prefixWord ++ tailWord_7414989).sum := by decide
  have hdescent : baseEnd_7414989 < baseStart_7414989 := by decide
  rcases family_descends (prefixWord ++ tailWord_7414989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7414991 : List Nat := [1, 1, 2, 1, 1, 3, 2, 2, 6, 1, 3]
def baseStart_7414991 : Nat := 118140960795 + 7414991 * 2 ^ 59
def prefixEnd_7414991 : Nat := 4983230072969 + 3 ^ 40 * 7414991 * 2
def baseEnd_7414991 : Nat := 3807454431762703547311583

theorem tailTrace_7414991 : CollatzResearch.WordTrace tailWord_7414991 prefixEnd_7414991 3807454431762703547311583 := by
  unfold tailWord_7414991
  simp only [CollatzResearch.WordTrace]
  refine ⟨270446939879761461486276827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180297959919840974324184551 270446939879761461486276827)
  ·
    refine ⟨405670409819642192229415241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270446939879761461486276827 405670409819642192229415241)
    ·
      refine ⟨304252807364731644172061431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 405670409819642192229415241 304252807364731644172061431)
      ·
        refine ⟨456379211047097466258092147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 304252807364731644172061431 456379211047097466258092147)
        ·
          refine ⟨684568816570646199387138221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 456379211047097466258092147 684568816570646199387138221)
          ·
            refine ⟨256713306213992324770176833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 684568816570646199387138221 256713306213992324770176833)
            ·
              refine ⟨192534979660494243577632625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 256713306213992324770176833 192534979660494243577632625)
              ·
                refine ⟨144401234745370682683224469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 192534979660494243577632625 144401234745370682683224469)
                ·
                  refine ⟨6768807878689250750776147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 144401234745370682683224469 6768807878689250750776147)
                  ·
                    refine ⟨10153211818033876126164221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6768807878689250750776147 10153211818033876126164221)
                    ·
                      refine ⟨3807454431762703547311583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10153211818033876126164221 3807454431762703547311583)
                      ·
                        rfl

theorem cell23_7414991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 2, 6, 1, 3].length) (baseStart_7414991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7414991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7414991 prefixEnd_7414991 := by exact prefixLift 7414991
  have htrace : WordTrace (prefixWord ++ tailWord_7414991) baseStart_7414991 baseEnd_7414991 := by
    simpa [prefixWord, tailWord_7414991, baseEnd_7414991] using wordTrace_append hprefix tailTrace_7414991
  have hstable : (prefixWord ++ tailWord_7414991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7414991).length < 2 ^ (prefixWord ++ tailWord_7414991).sum := by decide
  have hdescent : baseEnd_7414991 < baseStart_7414991 := by decide
  rcases family_descends (prefixWord ++ tailWord_7414991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7415026 : List Nat := [3, 2, 1, 3, 3, 2, 2, 2, 1, 2, 2]
def baseStart_7415026 : Nat := 118140960795 + 7415026 * 2 ^ 59
def prefixEnd_7415026 : Nat := 4983230072969 + 3 ^ 40 * 7415026 * 2
def baseEnd_7415026 : Nat := 3807472403585610910373923

theorem tailTrace_7415026 : CollatzResearch.WordTrace tailWord_7415026 prefixEnd_7415026 3807472403585610910373923 := by
  unfold tailWord_7415026
  simp only [CollatzResearch.WordTrace]
  refine ⟨67612054108658665615950233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 180298810956423108309200621 67612054108658665615950233)
  ·
    refine ⟨50709040581493999211962675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67612054108658665615950233 50709040581493999211962675)
    ·
      refine ⟨76063560872240998817944013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50709040581493999211962675 76063560872240998817944013)
      ·
        refine ⟨28523835327090374556729005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76063560872240998817944013 28523835327090374556729005)
        ·
          refine ⟨10696438247658890458773377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28523835327090374556729005 10696438247658890458773377)
          ·
            refine ⟨8022328685744167844080033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10696438247658890458773377 8022328685744167844080033)
            ·
              refine ⟨6016746514308125883060025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8022328685744167844080033 6016746514308125883060025)
              ·
                refine ⟨4512559885731094412295019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6016746514308125883060025 4512559885731094412295019)
                ·
                  refine ⟨6768839828596641618442529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4512559885731094412295019 6768839828596641618442529)
                  ·
                    refine ⟨5076629871447481213831897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6768839828596641618442529 5076629871447481213831897)
                    ·
                      refine ⟨3807472403585610910373923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5076629871447481213831897 3807472403585610910373923)
                      ·
                        rfl

theorem cell23_7415026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 2, 2, 2, 1, 2, 2].length) (baseStart_7415026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7415026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7415026 prefixEnd_7415026 := by exact prefixLift 7415026
  have htrace : WordTrace (prefixWord ++ tailWord_7415026) baseStart_7415026 baseEnd_7415026 := by
    simpa [prefixWord, tailWord_7415026, baseEnd_7415026] using wordTrace_append hprefix tailTrace_7415026
  have hstable : (prefixWord ++ tailWord_7415026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7415026).length < 2 ^ (prefixWord ++ tailWord_7415026).sum := by decide
  have hdescent : baseEnd_7415026 < baseStart_7415026 := by decide
  rcases family_descends (prefixWord ++ tailWord_7415026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7415041 : List Nat := [1, 2, 4, 1, 1, 4, 1, 1, 2, 6]
def baseStart_7415041 : Nat := 118140960795 + 7415041 * 2 ^ 59
def prefixEnd_7415041 : Nat := 4983230072969 + 3 ^ 40 * 7415041 * 2
def baseEnd_7415041 : Nat := 1269160035265142783895451

theorem tailTrace_7415041 : CollatzResearch.WordTrace tailWord_7415041 prefixEnd_7415041 1269160035265142783895451 := by
  unfold tailWord_7415041
  simp only [CollatzResearch.WordTrace]
  refine ⟨270448763529580320025596977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180299175686386880017064651 270448763529580320025596977)
  ·
    refine ⟨202836572647185240019197733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 270448763529580320025596977 202836572647185240019197733)
    ·
      refine ⟨38031857371347232503599575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 202836572647185240019197733 38031857371347232503599575)
      ·
        refine ⟨57047786057020848755399363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38031857371347232503599575 57047786057020848755399363)
        ·
          refine ⟨85571679085531273133099045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57047786057020848755399363 85571679085531273133099045)
          ·
            refine ⟨16044689828537113712456071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 85571679085531273133099045 16044689828537113712456071)
            ·
              refine ⟨24067034742805670568684107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16044689828537113712456071 24067034742805670568684107)
              ·
                refine ⟨36100552114208505853026161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24067034742805670568684107 36100552114208505853026161)
                ·
                  refine ⟨27075414085656379389769621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36100552114208505853026161 27075414085656379389769621)
                  ·
                    refine ⟨1269160035265142783895451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27075414085656379389769621 1269160035265142783895451)
                    ·
                      rfl

theorem cell23_7415041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 1, 1, 2, 6].length) (baseStart_7415041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7415041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7415041 prefixEnd_7415041 := by exact prefixLift 7415041
  have htrace : WordTrace (prefixWord ++ tailWord_7415041) baseStart_7415041 baseEnd_7415041 := by
    simpa [prefixWord, tailWord_7415041, baseEnd_7415041] using wordTrace_append hprefix tailTrace_7415041
  have hstable : (prefixWord ++ tailWord_7415041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7415041).length < 2 ^ (prefixWord ++ tailWord_7415041).sum := by decide
  have hdescent : baseEnd_7415041 < baseStart_7415041 := by decide
  rcases family_descends (prefixWord ++ tailWord_7415041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7415069 : List Nat := [1, 4, 2, 3, 1, 3, 2, 1, 1, 3, 2]
def baseStart_7415069 : Nat := 118140960795 + 7415069 * 2 ^ 59
def prefixEnd_7415069 : Nat := 4983230072969 + 3 ^ 40 * 7415069 * 2
def baseEnd_7415069 : Nat := 3807494483253754242136225

theorem tailTrace_7415069 : CollatzResearch.WordTrace tailWord_7415069 prefixEnd_7415069 3807494483253754242136225 := by
  unfold tailWord_7415069
  simp only [CollatzResearch.WordTrace]
  refine ⟨270449784773478880807616261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180299856515652587205077507 270449784773478880807616261)
  ·
    refine ⟨50709334645027290151428049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 270449784773478880807616261 50709334645027290151428049)
    ·
      refine ⟨38032000983770467613571037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50709334645027290151428049 38032000983770467613571037)
      ·
        refine ⟨14262000368913925355089139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38032000983770467613571037 14262000368913925355089139)
        ·
          refine ⟨21393000553370888032633709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14262000368913925355089139 21393000553370888032633709)
          ·
            refine ⟨8022375207514083012237641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21393000553370888032633709 8022375207514083012237641)
            ·
              refine ⟨6016781405635562259178231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8022375207514083012237641 6016781405635562259178231)
              ·
                refine ⟨9025172108453343388767347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6016781405635562259178231 9025172108453343388767347)
                ·
                  refine ⟨13537758162680015083151021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9025172108453343388767347 13537758162680015083151021)
                  ·
                    refine ⟨5076659311005005656181633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13537758162680015083151021 5076659311005005656181633)
                    ·
                      refine ⟨3807494483253754242136225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5076659311005005656181633 3807494483253754242136225)
                      ·
                        rfl

theorem cell23_7415069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 3, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 3, 2, 1, 1, 3, 2].length) (baseStart_7415069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7415069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7415069 prefixEnd_7415069 := by exact prefixLift 7415069
  have htrace : WordTrace (prefixWord ++ tailWord_7415069) baseStart_7415069 baseEnd_7415069 := by
    simpa [prefixWord, tailWord_7415069, baseEnd_7415069] using wordTrace_append hprefix tailTrace_7415069
  have hstable : (prefixWord ++ tailWord_7415069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7415069).length < 2 ^ (prefixWord ++ tailWord_7415069).sum := by decide
  have hdescent : baseEnd_7415069 < baseStart_7415069 := by decide
  rcases family_descends (prefixWord ++ tailWord_7415069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7415082 : List Nat := [3, 1, 4, 2, 1, 2, 1, 1, 4, 2, 2]
def baseStart_7415082 : Nat := 118140960795 + 7415082 * 2 ^ 59
def prefixEnd_7415082 : Nat := 4983230072969 + 3 ^ 40 * 7415082 * 2
def baseEnd_7415082 : Nat := 3807501158502262691273665

theorem tailTrace_7415082 : CollatzResearch.WordTrace tailWord_7415082 prefixEnd_7415082 3807501158502262691273665 := by
  unfold tailWord_7415082
  simp only [CollatzResearch.WordTrace]
  refine ⟨67612564730607946006959875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 180300172614954522685226333 67612564730607946006959875)
  ·
    refine ⟨101418847095911919010439813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67612564730607946006959875 101418847095911919010439813)
    ·
      refine ⟨19016033830483484814457465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 101418847095911919010439813 19016033830483484814457465)
      ·
        refine ⟨14262025372862613610843099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19016033830483484814457465 14262025372862613610843099)
        ·
          refine ⟨21393038059293920416264649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14262025372862613610843099 21393038059293920416264649)
          ·
            refine ⟨16044778544470440312198487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21393038059293920416264649 16044778544470440312198487)
            ·
              refine ⟨24067167816705660468297731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16044778544470440312198487 24067167816705660468297731)
              ·
                refine ⟨36100751725058490702446597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24067167816705660468297731 36100751725058490702446597)
                ·
                  refine ⟨6768890948448467006708737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36100751725058490702446597 6768890948448467006708737)
                  ·
                    refine ⟨5076668211336350255031553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6768890948448467006708737 5076668211336350255031553)
                    ·
                      refine ⟨3807501158502262691273665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5076668211336350255031553 3807501158502262691273665)
                      ·
                        rfl

theorem cell23_7415082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 1, 1, 4, 2, 2].length) (baseStart_7415082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7415082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7415082 prefixEnd_7415082 := by exact prefixLift 7415082
  have htrace : WordTrace (prefixWord ++ tailWord_7415082) baseStart_7415082 baseEnd_7415082 := by
    simpa [prefixWord, tailWord_7415082, baseEnd_7415082] using wordTrace_append hprefix tailTrace_7415082
  have hstable : (prefixWord ++ tailWord_7415082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7415082).length < 2 ^ (prefixWord ++ tailWord_7415082).sum := by decide
  have hdescent : baseEnd_7415082 < baseStart_7415082 := by decide
  rcases family_descends (prefixWord ++ tailWord_7415082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7415121 : List Nat := [1, 2, 2, 1, 4, 1, 1, 3, 1, 3, 4]
def baseStart_7415121 : Nat := 118140960795 + 7415121 * 2 ^ 59
def prefixEnd_7415121 : Nat := 4983230072969 + 3 ^ 40 * 7415121 * 2
def baseEnd_7415121 : Nat := 3807521184247788038685985

theorem tailTrace_7415121 : CollatzResearch.WordTrace tailWord_7415121 prefixEnd_7415121 3807521184247788038685985 := by
  unfold tailWord_7415121
  simp only [CollatzResearch.WordTrace]
  refine ⟨270451681369290493688509217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180301120912860329125672811 270451681369290493688509217)
  ·
    refine ⟨202838761026967870266381913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 270451681369290493688509217 202838761026967870266381913)
    ·
      refine ⟨152129070770225902699786435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 202838761026967870266381913 152129070770225902699786435)
      ·
        refine ⟨228193606155338854049679653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152129070770225902699786435 228193606155338854049679653)
        ·
          refine ⟨42786301154126035134314935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 228193606155338854049679653 42786301154126035134314935)
          ·
            refine ⟨64179451731189052701472403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42786301154126035134314935 64179451731189052701472403)
            ·
              refine ⟨96269177596783579052208605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64179451731189052701472403 96269177596783579052208605)
              ·
                refine ⟨36100941598793842144578227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 96269177596783579052208605 36100941598793842144578227)
                ·
                  refine ⟨54151412398190763216867341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36100941598793842144578227 54151412398190763216867341)
                  ·
                    refine ⟨20306779649321536206325253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 54151412398190763216867341 20306779649321536206325253)
                    ·
                      refine ⟨3807521184247788038685985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20306779649321536206325253 3807521184247788038685985)
                      ·
                        rfl

theorem cell23_7415121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 3, 1, 3, 4].length) (baseStart_7415121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7415121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7415121 prefixEnd_7415121 := by exact prefixLift 7415121
  have htrace : WordTrace (prefixWord ++ tailWord_7415121) baseStart_7415121 baseEnd_7415121 := by
    simpa [prefixWord, tailWord_7415121, baseEnd_7415121] using wordTrace_append hprefix tailTrace_7415121
  have hstable : (prefixWord ++ tailWord_7415121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7415121).length < 2 ^ (prefixWord ++ tailWord_7415121).sum := by decide
  have hdescent : baseEnd_7415121 < baseStart_7415121 := by decide
  rcases family_descends (prefixWord ++ tailWord_7415121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7415175 : List Nat := [1, 1, 4, 2, 2, 3, 2, 1, 2, 2, 3]
def baseStart_7415175 : Nat := 118140960795 + 7415175 * 2 ^ 59
def prefixEnd_7415175 : Nat := 4983230072969 + 3 ^ 40 * 7415175 * 2
def baseEnd_7415175 : Nat := 3807548912203130827410737

theorem tailTrace_7415175 : CollatzResearch.WordTrace tailWord_7415175 prefixEnd_7415175 3807548912203130827410737 := by
  unfold tailWord_7415175
  simp only [CollatzResearch.WordTrace]
  refine ⟨270453650911094860910974979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180302433940729907273983319 270453650911094860910974979)
  ·
    refine ⟨405680476366642291366462469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270453650911094860910974979 405680476366642291366462469)
    ·
      refine ⟨76065089318745429631211713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 405680476366642291366462469 76065089318745429631211713)
      ·
        refine ⟨57048816989059072223408785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76065089318745429631211713 57048816989059072223408785)
        ·
          refine ⟨42786612741794304167556589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57048816989059072223408785 42786612741794304167556589)
          ·
            refine ⟨16044979778172864062833721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42786612741794304167556589 16044979778172864062833721)
            ·
              refine ⟨12033734833629648047125291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16044979778172864062833721 12033734833629648047125291)
              ·
                refine ⟨18050602250444472070687937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12033734833629648047125291 18050602250444472070687937)
                ·
                  refine ⟨13537951687833354053015953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18050602250444472070687937 13537951687833354053015953)
                  ·
                    refine ⟨10153463765875015539761965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13537951687833354053015953 10153463765875015539761965)
                    ·
                      refine ⟨3807548912203130827410737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10153463765875015539761965 3807548912203130827410737)
                      ·
                        rfl

theorem cell23_7415175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 2, 1, 2, 2, 3].length) (baseStart_7415175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7415175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7415175 prefixEnd_7415175 := by exact prefixLift 7415175
  have htrace : WordTrace (prefixWord ++ tailWord_7415175) baseStart_7415175 baseEnd_7415175 := by
    simpa [prefixWord, tailWord_7415175, baseEnd_7415175] using wordTrace_append hprefix tailTrace_7415175
  have hstable : (prefixWord ++ tailWord_7415175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7415175).length < 2 ^ (prefixWord ++ tailWord_7415175).sum := by decide
  have hdescent : baseEnd_7415175 < baseStart_7415175 := by decide
  rcases family_descends (prefixWord ++ tailWord_7415175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7415199 : List Nat := [1, 1, 2, 5, 1, 4, 2, 2, 1, 4]
def baseStart_7415199 : Nat := 118140960795 + 7415199 * 2 ^ 59
def prefixEnd_7415199 : Nat := 4983230072969 + 3 ^ 40 * 7415199 * 2
def baseEnd_7415199 : Nat := 1269187078579612911170209

theorem tailTrace_7415199 : CollatzResearch.WordTrace tailWord_7415199 prefixEnd_7415199 1269187078579612911170209 := by
  unfold tailWord_7415199
  simp only [CollatzResearch.WordTrace]
  refine ⟨270454526263007913009848651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180303017508671942006565767 270454526263007913009848651)
  ·
    refine ⟨405681789394511869514772977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270454526263007913009848651 405681789394511869514772977)
    ·
      refine ⟨304261342045883902136079733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 405681789394511869514772977 304261342045883902136079733)
      ·
        refine ⟨28524500816801615825257475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 304261342045883902136079733 28524500816801615825257475)
        ·
          refine ⟨42786751225202423737886213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28524500816801615825257475 42786751225202423737886213)
          ·
            refine ⟨8022515854725454450853665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42786751225202423737886213 8022515854725454450853665)
            ·
              refine ⟨6016886891044090838140249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8022515854725454450853665 6016886891044090838140249)
              ·
                refine ⟨4512665168283068128605187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6016886891044090838140249 4512665168283068128605187)
                ·
                  refine ⟨6768997752424602192907781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4512665168283068128605187 6768997752424602192907781)
                  ·
                    refine ⟨1269187078579612911170209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6768997752424602192907781 1269187078579612911170209)
                    ·
                      rfl

theorem cell23_7415199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 4, 2, 2, 1, 4].length) (baseStart_7415199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7415199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7415199 prefixEnd_7415199 := by exact prefixLift 7415199
  have htrace : WordTrace (prefixWord ++ tailWord_7415199) baseStart_7415199 baseEnd_7415199 := by
    simpa [prefixWord, tailWord_7415199, baseEnd_7415199] using wordTrace_append hprefix tailTrace_7415199
  have hstable : (prefixWord ++ tailWord_7415199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7415199).length < 2 ^ (prefixWord ++ tailWord_7415199).sum := by decide
  have hdescent : baseEnd_7415199 < baseStart_7415199 := by decide
  rcases family_descends (prefixWord ++ tailWord_7415199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7415241 : List Nat := [1, 2, 1, 1, 2, 1, 3, 2, 3, 1, 6]
def baseStart_7415241 : Nat := 118140960795 + 7415241 * 2 ^ 59
def prefixEnd_7415241 : Nat := 4983230072969 + 3 ^ 40 * 7415241 * 2
def baseEnd_7415241 : Nat := 3807582801926327569185433

theorem tailTrace_7415241 : CollatzResearch.WordTrace tailWord_7415241 prefixEnd_7415241 3807582801926327569185433 := by
  unfold tailWord_7415241
  simp only [CollatzResearch.WordTrace]
  refine ⟨270456058128855754182877577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180304038752570502788585051 270456058128855754182877577)
  ·
    refine ⟨202842043596641815637158183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 270456058128855754182877577 202842043596641815637158183)
    ·
      refine ⟨304263065394962723455737275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202842043596641815637158183 304263065394962723455737275)
      ·
        refine ⟨456394598092444085183605913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 304263065394962723455737275 456394598092444085183605913)
        ·
          refine ⟨342295948569333063887704435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 456394598092444085183605913 342295948569333063887704435)
          ·
            refine ⟨513443922853999595831556653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 342295948569333063887704435 513443922853999595831556653)
            ·
              refine ⟨192541471070249848436833745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 513443922853999595831556653 192541471070249848436833745)
              ·
                refine ⟨144406103302687386327625309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 192541471070249848436833745 144406103302687386327625309)
                ·
                  refine ⟨54152288738507769872859491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 144406103302687386327625309 54152288738507769872859491)
                  ·
                    refine ⟨81228433107761654809289237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 54152288738507769872859491 81228433107761654809289237)
                    ·
                      refine ⟨3807582801926327569185433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 81228433107761654809289237 3807582801926327569185433)
                      ·
                        rfl

theorem cell23_7415241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 2, 3, 1, 6].length) (baseStart_7415241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7415241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7415241 prefixEnd_7415241 := by exact prefixLift 7415241
  have htrace : WordTrace (prefixWord ++ tailWord_7415241) baseStart_7415241 baseEnd_7415241 := by
    simpa [prefixWord, tailWord_7415241, baseEnd_7415241] using wordTrace_append hprefix tailTrace_7415241
  have hstable : (prefixWord ++ tailWord_7415241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7415241).length < 2 ^ (prefixWord ++ tailWord_7415241).sum := by decide
  have hdescent : baseEnd_7415241 < baseStart_7415241 := by decide
  rcases family_descends (prefixWord ++ tailWord_7415241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7415242 : List Nat := [3, 1, 2, 1, 2, 5, 2, 1, 1, 5]
def baseStart_7415242 : Nat := 118140960795 + 7415242 * 2 ^ 59
def prefixEnd_7415242 : Nat := 4983230072969 + 3 ^ 40 * 7415242 * 2
def baseEnd_7415242 : Nat := 1269194438468994021757643

theorem tailTrace_7415242 : CollatzResearch.WordTrace tailWord_7415242 prefixEnd_7415242 1269194438468994021757643 := by
  unfold tailWord_7415242
  simp only [CollatzResearch.WordTrace]
  refine ⟨67614023650463032838415995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 180304063067901420902442653 67614023650463032838415995)
  ·
    refine ⟨101421035475694549257623993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67614023650463032838415995 101421035475694549257623993)
    ·
      refine ⟨76065776606770911943217995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101421035475694549257623993 76065776606770911943217995)
      ·
        refine ⟨114098664910156367914826993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76065776606770911943217995 114098664910156367914826993)
        ·
          refine ⟨85573998682617275936120245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114098664910156367914826993 85573998682617275936120245)
          ·
            refine ⟨8022562376495369619011273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 85573998682617275936120245 8022562376495369619011273)
            ·
              refine ⟨6016921782371527214258455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8022562376495369619011273 6016921782371527214258455)
              ·
                refine ⟨9025382673557290821387683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6016921782371527214258455 9025382673557290821387683)
                ·
                  refine ⟨13538074010335936232081525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9025382673557290821387683 13538074010335936232081525)
                  ·
                    refine ⟨1269194438468994021757643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13538074010335936232081525 1269194438468994021757643)
                    ·
                      rfl

theorem cell23_7415242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 5, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 5, 2, 1, 1, 5].length) (baseStart_7415242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7415242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7415242 prefixEnd_7415242 := by exact prefixLift 7415242
  have htrace : WordTrace (prefixWord ++ tailWord_7415242) baseStart_7415242 baseEnd_7415242 := by
    simpa [prefixWord, tailWord_7415242, baseEnd_7415242] using wordTrace_append hprefix tailTrace_7415242
  have hstable : (prefixWord ++ tailWord_7415242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7415242).length < 2 ^ (prefixWord ++ tailWord_7415242).sum := by decide
  have hdescent : baseEnd_7415242 < baseStart_7415242 := by decide
  rcases family_descends (prefixWord ++ tailWord_7415242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7415272 : List Nat := [2, 1, 4, 1, 1, 2, 5, 1, 2, 4]
def baseStart_7415272 : Nat := 118140960795 + 7415272 * 2 ^ 59
def prefixEnd_7415272 : Nat := 4983230072969 + 3 ^ 40 * 7415272 * 2
def baseEnd_7415272 : Nat := 1269199573275538982632597

theorem tailTrace_7415272 : CollatzResearch.WordTrace tailWord_7415272 prefixEnd_7415272 1269199573275538982632597 := by
  unfold tailWord_7415272
  simp only [CollatzResearch.WordTrace]
  refine ⟨135228594395871723238628035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180304792527828964318170713 135228594395871723238628035)
  ·
    refine ⟨202842891593807584857942053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135228594395871723238628035 202842891593807584857942053)
    ·
      refine ⟨38033042173838922160864135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 202842891593807584857942053 38033042173838922160864135)
      ·
        refine ⟨57049563260758383241296203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38033042173838922160864135 57049563260758383241296203)
        ·
          refine ⟨85574344891137574861944305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57049563260758383241296203 85574344891137574861944305)
          ·
            refine ⟨64180758668353181146458229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85574344891137574861944305 64180758668353181146458229)
            ·
              refine ⟨6016946125158110732480459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 64180758668353181146458229 6016946125158110732480459)
              ·
                refine ⟨9025419187737166098720689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6016946125158110732480459 9025419187737166098720689)
                ·
                  refine ⟨6769064390802874574040517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9025419187737166098720689 6769064390802874574040517)
                  ·
                    refine ⟨1269199573275538982632597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6769064390802874574040517 1269199573275538982632597)
                    ·
                      rfl

theorem cell23_7415272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 5, 1, 2, 4].length) (baseStart_7415272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7415272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7415272 prefixEnd_7415272 := by exact prefixLift 7415272
  have htrace : WordTrace (prefixWord ++ tailWord_7415272) baseStart_7415272 baseEnd_7415272 := by
    simpa [prefixWord, tailWord_7415272, baseEnd_7415272] using wordTrace_append hprefix tailTrace_7415272
  have hstable : (prefixWord ++ tailWord_7415272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7415272).length < 2 ^ (prefixWord ++ tailWord_7415272).sum := by decide
  have hdescent : baseEnd_7415272 < baseStart_7415272 := by decide
  rcases family_descends (prefixWord ++ tailWord_7415272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7415282 : List Nat := [3, 2, 1, 4, 1, 1, 1, 4, 1, 2, 3]
def baseStart_7415282 : Nat := 118140960795 + 7415282 * 2 ^ 59
def prefixEnd_7415282 : Nat := 4983230072969 + 3 ^ 40 * 7415282 * 2
def baseEnd_7415282 : Nat := 3807603854633161908772745

theorem tailTrace_7415282 : CollatzResearch.WordTrace tailWord_7415282 prefixEnd_7415282 3807603854633161908772745 := by
  unfold tailWord_7415282
  simp only [CollatzResearch.WordTrace]
  refine ⟨67614388380426804546280025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 180305035681138145456746733 67614388380426804546280025)
  ·
    refine ⟨50710791285320103409710019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67614388380426804546280025 50710791285320103409710019)
    ·
      refine ⟨76066186927980155114565029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50710791285320103409710019 76066186927980155114565029)
      ·
        refine ⟨14262410048996279083980943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 76066186927980155114565029 14262410048996279083980943)
        ·
          refine ⟨21393615073494418625971415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14262410048996279083980943 21393615073494418625971415)
          ·
            refine ⟨32090422610241627938957123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21393615073494418625971415 32090422610241627938957123)
            ·
              refine ⟨48135633915362441908435685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32090422610241627938957123 48135633915362441908435685)
              ·
                refine ⟨9025431359130457857831691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48135633915362441908435685 9025431359130457857831691)
                ·
                  refine ⟨13538147038695686786747537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9025431359130457857831691 13538147038695686786747537)
                  ·
                    refine ⟨10153610279021765090060653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13538147038695686786747537 10153610279021765090060653)
                    ·
                      refine ⟨3807603854633161908772745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10153610279021765090060653 3807603854633161908772745)
                      ·
                        rfl

theorem cell23_7415282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 1, 4, 1, 2, 3].length) (baseStart_7415282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7415282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7415282 prefixEnd_7415282 := by exact prefixLift 7415282
  have htrace : WordTrace (prefixWord ++ tailWord_7415282) baseStart_7415282 baseEnd_7415282 := by
    simpa [prefixWord, tailWord_7415282, baseEnd_7415282] using wordTrace_append hprefix tailTrace_7415282
  have hstable : (prefixWord ++ tailWord_7415282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7415282).length < 2 ^ (prefixWord ++ tailWord_7415282).sum := by decide
  have hdescent : baseEnd_7415282 < baseStart_7415282 := by decide
  rcases family_descends (prefixWord ++ tailWord_7415282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
