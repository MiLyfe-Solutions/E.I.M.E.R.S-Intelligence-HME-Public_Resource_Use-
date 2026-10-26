import V185TrunkScan23Chunk0480

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_2845087 : List Nat := [1, 1, 2, 5, 1, 1, 2, 3, 3, 4]
def baseStart_2845087 : Nat := 118140960795 + 2845087 * 2 ^ 59
def prefixEnd_2845087 : Nat := 4983230072969 + 3 ^ 40 * 2845087 * 2
def baseEnd_2845087 : Nat := 486965711619471772576063

theorem tailTrace_2845087 : CollatzResearch.WordTrace tailWord_2845087 prefixEnd_2845087 486965711619471772576063 := by
  unfold tailWord_2845087
  simp only [CollatzResearch.WordTrace]
  refine ⟨103768847843743176020061515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69179231895828784013374343 103768847843743176020061515)
  ·
    refine ⟨155653271765614764030092273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103768847843743176020061515 155653271765614764030092273)
    ·
      refine ⟨116739953824211073022569205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 155653271765614764030092273 116739953824211073022569205)
      ·
        refine ⟨10944370671019788095865863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 116739953824211073022569205 10944370671019788095865863)
        ·
          refine ⟨16416556006529682143798795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10944370671019788095865863 16416556006529682143798795)
          ·
            refine ⟨24624834009794523215698193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16416556006529682143798795 24624834009794523215698193)
            ·
              refine ⟨18468625507345892411773645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24624834009794523215698193 18468625507345892411773645)
              ·
                refine ⟨6925734565254709654415117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18468625507345892411773645 6925734565254709654415117)
                ·
                  refine ⟨2597150461970516120405669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6925734565254709654415117 2597150461970516120405669)
                  ·
                    refine ⟨486965711619471772576063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2597150461970516120405669 486965711619471772576063)
                    ·
                      rfl

theorem cell23_2845087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 2, 3, 3, 4].length) (baseStart_2845087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2845087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2845087 prefixEnd_2845087 := by exact prefixLift 2845087
  have htrace : WordTrace (prefixWord ++ tailWord_2845087) baseStart_2845087 baseEnd_2845087 := by
    simpa [prefixWord, tailWord_2845087, baseEnd_2845087] using wordTrace_append hprefix tailTrace_2845087
  have hstable : (prefixWord ++ tailWord_2845087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2845087).length < 2 ^ (prefixWord ++ tailWord_2845087).sum := by decide
  have hdescent : baseEnd_2845087 < baseStart_2845087 := by decide
  rcases family_descends (prefixWord ++ tailWord_2845087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2845108 : List Nat := [2, 5, 2, 2, 1, 2, 1, 1, 2, 5]
def baseStart_2845108 : Nat := 118140960795 + 2845108 * 2 ^ 59
def prefixEnd_2845108 : Nat := 4983230072969 + 3 ^ 40 * 2845108 * 2
def baseEnd_2845108 : Nat := 486969305984053245188531

theorem tailTrace_2845108 : CollatzResearch.WordTrace tailWord_2845108 prefixEnd_2845108 486969305984053245188531 := by
  unfold tailWord_2845108
  simp only [CollatzResearch.WordTrace]
  refine ⟨51884806888333548303287989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69179742517778064404383985 51884806888333548303287989)
  ·
    refine ⟨4864200645781270153433249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 51884806888333548303287989 4864200645781270153433249)
    ·
      refine ⟨3648150484335952615074937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4864200645781270153433249 3648150484335952615074937)
      ·
        refine ⟨2736112863251964461306203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3648150484335952615074937 2736112863251964461306203)
        ·
          refine ⟨4104169294877946691959305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2736112863251964461306203 4104169294877946691959305)
          ·
            refine ⟨3078126971158460018969479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4104169294877946691959305 3078126971158460018969479)
            ·
              refine ⟨4617190456737690028454219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3078126971158460018969479 4617190456737690028454219)
              ·
                refine ⟨6925785685106535042681329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4617190456737690028454219 6925785685106535042681329)
                ·
                  refine ⟨5194339263829901282010997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6925785685106535042681329 5194339263829901282010997)
                  ·
                    refine ⟨486969305984053245188531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5194339263829901282010997 486969305984053245188531)
                    ·
                      rfl

theorem cell23_2845108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 2, 1, 1, 2, 5].length) (baseStart_2845108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2845108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2845108 prefixEnd_2845108 := by exact prefixLift 2845108
  have htrace : WordTrace (prefixWord ++ tailWord_2845108) baseStart_2845108 baseEnd_2845108 := by
    simpa [prefixWord, tailWord_2845108, baseEnd_2845108] using wordTrace_append hprefix tailTrace_2845108
  have hstable : (prefixWord ++ tailWord_2845108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2845108).length < 2 ^ (prefixWord ++ tailWord_2845108).sum := by decide
  have hdescent : baseEnd_2845108 < baseStart_2845108 := by decide
  rcases family_descends (prefixWord ++ tailWord_2845108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2845167 : List Nat := [1, 1, 2, 1, 4, 1, 1, 1, 1, 8, 2]
def baseStart_2845167 : Nat := 118140960795 + 2845167 * 2 ^ 59
def prefixEnd_2845167 : Nat := 4983230072969 + 3 ^ 40 * 2845167 * 2
def baseEnd_2845167 : Nat := 1460938213310775004727821

theorem tailTrace_2845167 : CollatzResearch.WordTrace tailWord_2845167 prefixEnd_2845167 1460938213310775004727821 := by
  unfold tailWord_2845167
  simp only [CollatzResearch.WordTrace]
  refine ⟨103771765683453349682973755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69181177122302233121982503 103771765683453349682973755)
  ·
    refine ⟨155657648525180024524460633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103771765683453349682973755 155657648525180024524460633)
    ·
      refine ⟨116743236393885018393345475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 155657648525180024524460633 116743236393885018393345475)
      ·
        refine ⟨175114854590827527590018213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116743236393885018393345475 175114854590827527590018213)
        ·
          refine ⟨32834035235780161423128415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 175114854590827527590018213 32834035235780161423128415)
          ·
            refine ⟨49251052853670242134692623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32834035235780161423128415 49251052853670242134692623)
            ·
              refine ⟨73876579280505363202038935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49251052853670242134692623 73876579280505363202038935)
              ·
                refine ⟨110814868920758044803058403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 73876579280505363202038935 110814868920758044803058403)
                ·
                  refine ⟨166222303381137067204587605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 110814868920758044803058403 166222303381137067204587605)
                  ·
                    refine ⟨1947917617747700006303761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 166222303381137067204587605 1947917617747700006303761)
                    ·
                      refine ⟨1460938213310775004727821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1947917617747700006303761 1460938213310775004727821)
                      ·
                        rfl

theorem cell23_2845167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 1, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 1, 1, 8, 2].length) (baseStart_2845167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2845167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2845167 prefixEnd_2845167 := by exact prefixLift 2845167
  have htrace : WordTrace (prefixWord ++ tailWord_2845167) baseStart_2845167 baseEnd_2845167 := by
    simpa [prefixWord, tailWord_2845167, baseEnd_2845167] using wordTrace_append hprefix tailTrace_2845167
  have hstable : (prefixWord ++ tailWord_2845167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2845167).length < 2 ^ (prefixWord ++ tailWord_2845167).sum := by decide
  have hdescent : baseEnd_2845167 < baseStart_2845167 := by decide
  rcases family_descends (prefixWord ++ tailWord_2845167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2845177 : List Nat := [1, 2, 1, 3, 1, 2, 3, 2, 4, 4]
def baseStart_2845177 : Nat := 118140960795 + 2845177 * 2 ^ 59
def prefixEnd_2845177 : Nat := 4983230072969 + 3 ^ 40 * 2845177 * 2
def baseEnd_2845177 : Nat := 486981116039106655200925

theorem tailTrace_2845177 : CollatzResearch.WordTrace tailWord_2845177 prefixEnd_2845177 486981116039106655200925 := by
  unfold tailWord_2845177
  simp only [CollatzResearch.WordTrace]
  refine ⟨103772130413417121390837785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69181420275611414260558523 103772130413417121390837785)
  ·
    refine ⟨77829097810062841043128339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103772130413417121390837785 77829097810062841043128339)
    ·
      refine ⟨116743646715094261564692509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77829097810062841043128339 116743646715094261564692509)
      ·
        refine ⟨43778867518160348086759691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 116743646715094261564692509 43778867518160348086759691)
        ·
          refine ⟨65668301277240522130139537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43778867518160348086759691 65668301277240522130139537)
          ·
            refine ⟨49251225957930391597604653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65668301277240522130139537 49251225957930391597604653)
            ·
              refine ⟨18469209734223896849101745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49251225957930391597604653 18469209734223896849101745)
              ·
                refine ⟨13851907300667922636826309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18469209734223896849101745 13851907300667922636826309)
                ·
                  refine ⟨2597232618875235494404933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13851907300667922636826309 2597232618875235494404933)
                  ·
                    refine ⟨486981116039106655200925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2597232618875235494404933 486981116039106655200925)
                    ·
                      rfl

theorem cell23_2845177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 3, 2, 4, 4].length) (baseStart_2845177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2845177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2845177 prefixEnd_2845177 := by exact prefixLift 2845177
  have htrace : WordTrace (prefixWord ++ tailWord_2845177) baseStart_2845177 baseEnd_2845177 := by
    simpa [prefixWord, tailWord_2845177, baseEnd_2845177] using wordTrace_append hprefix tailTrace_2845177
  have hstable : (prefixWord ++ tailWord_2845177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2845177).length < 2 ^ (prefixWord ++ tailWord_2845177).sum := by decide
  have hdescent : baseEnd_2845177 < baseStart_2845177 := by decide
  rcases family_descends (prefixWord ++ tailWord_2845177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2845187 : List Nat := [1, 1, 1, 3, 2, 1, 6, 1, 1, 1, 5]
def baseStart_2845187 : Nat := 118140960795 + 2845187 * 2 ^ 59
def prefixEnd_2845187 : Nat := 4983230072969 + 3 ^ 40 * 2845187 * 2
def baseEnd_2845187 : Nat := 1460948482923864926477729

theorem tailTrace_2845187 : CollatzResearch.WordTrace tailWord_2845187 prefixEnd_2845187 1460948482923864926477729 := by
  unfold tailWord_2845187
  simp only [CollatzResearch.WordTrace]
  refine ⟨103772495143380893098701815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69181663428920595399134543 103772495143380893098701815)
  ·
    refine ⟨155658742715071339648052723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103772495143380893098701815 155658742715071339648052723)
    ·
      refine ⟨233488114072607009472079085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155658742715071339648052723 233488114072607009472079085)
      ·
        refine ⟨87558042777227628552029657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 233488114072607009472079085 87558042777227628552029657)
        ·
          refine ⟨65668532082920721414022243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87558042777227628552029657 65668532082920721414022243)
          ·
            refine ⟨98502798124381082121033365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65668532082920721414022243 98502798124381082121033365)
            ·
              refine ⟨4617318662080363224423439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 98502798124381082121033365 4617318662080363224423439)
              ·
                refine ⟨6925977993120544836635159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4617318662080363224423439 6925977993120544836635159)
                ·
                  refine ⟨10388966989680817254952739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6925977993120544836635159 10388966989680817254952739)
                  ·
                    refine ⟨15583450484521225882429109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10388966989680817254952739 15583450484521225882429109)
                    ·
                      refine ⟨1460948482923864926477729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15583450484521225882429109 1460948482923864926477729)
                      ·
                        rfl

theorem cell23_2845187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 6, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 6, 1, 1, 1, 5].length) (baseStart_2845187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2845187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2845187 prefixEnd_2845187 := by exact prefixLift 2845187
  have htrace : WordTrace (prefixWord ++ tailWord_2845187) baseStart_2845187 baseEnd_2845187 := by
    simpa [prefixWord, tailWord_2845187, baseEnd_2845187] using wordTrace_append hprefix tailTrace_2845187
  have hstable : (prefixWord ++ tailWord_2845187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2845187).length < 2 ^ (prefixWord ++ tailWord_2845187).sum := by decide
  have hdescent : baseEnd_2845187 < baseStart_2845187 := by decide
  rcases family_descends (prefixWord ++ tailWord_2845187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2845194 : List Nat := [3, 1, 2, 2, 2, 1, 2, 4, 2, 4]
def baseStart_2845194 : Nat := 118140960795 + 2845194 * 2 ^ 59
def prefixEnd_2845194 : Nat := 4983230072969 + 3 ^ 40 * 2845194 * 2
def baseEnd_2845194 : Nat := 486984025762815466363399

theorem tailTrace_2845194 : CollatzResearch.WordTrace tailWord_2845194 prefixEnd_2845194 486984025762815466363399 := by
  unfold tailWord_2845194
  simp only [CollatzResearch.WordTrace]
  refine ⟨25943187613588883323551659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69181833636237022196137757 25943187613588883323551659)
  ·
    refine ⟨38914781420383324985327489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25943187613588883323551659 38914781420383324985327489)
    ·
      refine ⟨29186086065287493738995617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38914781420383324985327489 29186086065287493738995617)
      ·
        refine ⟨21889564548965620304246713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29186086065287493738995617 21889564548965620304246713)
        ·
          refine ⟨16417173411724215228185035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21889564548965620304246713 16417173411724215228185035)
          ·
            refine ⟨24625760117586322842277553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16417173411724215228185035 24625760117586322842277553)
            ·
              refine ⟨18469320088189742131708165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24625760117586322842277553 18469320088189742131708165)
              ·
                refine ⟨3462997516535576649695281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18469320088189742131708165 3462997516535576649695281)
                ·
                  refine ⟨2597248137401682487271461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3462997516535576649695281 2597248137401682487271461)
                  ·
                    refine ⟨486984025762815466363399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2597248137401682487271461 486984025762815466363399)
                    ·
                      rfl

theorem cell23_2845194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 2, 4, 2, 4].length) (baseStart_2845194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2845194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2845194 prefixEnd_2845194 := by exact prefixLift 2845194
  have htrace : WordTrace (prefixWord ++ tailWord_2845194) baseStart_2845194 baseEnd_2845194 := by
    simpa [prefixWord, tailWord_2845194, baseEnd_2845194] using wordTrace_append hprefix tailTrace_2845194
  have hstable : (prefixWord ++ tailWord_2845194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2845194).length < 2 ^ (prefixWord ++ tailWord_2845194).sum := by decide
  have hdescent : baseEnd_2845194 < baseStart_2845194 := by decide
  rcases family_descends (prefixWord ++ tailWord_2845194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2845234 : List Nat := [3, 2, 1, 1, 2, 1, 2, 1, 6, 1, 3]
def baseStart_2845234 : Nat := 118140960795 + 2845234 * 2 ^ 59
def prefixEnd_2845234 : Nat := 4983230072969 + 3 ^ 40 * 2845234 * 2
def baseEnd_2845234 : Nat := 1460972616514626242590013

theorem tailTrace_2845234 : CollatzResearch.WordTrace tailWord_2845234 prefixEnd_2845234 1460972616514626242590013 := by
  unfold tailWord_2845234
  simp only [CollatzResearch.WordTrace]
  refine ⟨25943552343552655031415689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69182806249473746750441837 25943552343552655031415689)
  ·
    refine ⟨19457664257664491273561767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25943552343552655031415689 19457664257664491273561767)
    ·
      refine ⟨29186496386496736910342651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19457664257664491273561767 29186496386496736910342651)
      ·
        refine ⟨43779744579745105365513977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29186496386496736910342651 43779744579745105365513977)
        ·
          refine ⟨32834808434808829024135483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43779744579745105365513977 32834808434808829024135483)
          ·
            refine ⟨49252212652213243536203225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32834808434808829024135483 49252212652213243536203225)
            ·
              refine ⟨36939159489159932652152419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49252212652213243536203225 36939159489159932652152419)
              ·
                refine ⟨55408739233739898978228629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36939159489159932652152419 55408739233739898978228629)
                ·
                  refine ⟨2597284651581557764604467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 55408739233739898978228629 2597284651581557764604467)
                  ·
                    refine ⟨3895926977372336646906701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2597284651581557764604467 3895926977372336646906701)
                    ·
                      refine ⟨1460972616514626242590013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3895926977372336646906701 1460972616514626242590013)
                      ·
                        rfl

theorem cell23_2845234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 1, 6, 1, 3].length) (baseStart_2845234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2845234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2845234 prefixEnd_2845234 := by exact prefixLift 2845234
  have htrace : WordTrace (prefixWord ++ tailWord_2845234) baseStart_2845234 baseEnd_2845234 := by
    simpa [prefixWord, tailWord_2845234, baseEnd_2845234] using wordTrace_append hprefix tailTrace_2845234
  have hstable : (prefixWord ++ tailWord_2845234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2845234).length < 2 ^ (prefixWord ++ tailWord_2845234).sum := by decide
  have hdescent : baseEnd_2845234 < baseStart_2845234 := by decide
  rcases family_descends (prefixWord ++ tailWord_2845234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2845287 : List Nat := [1, 1, 5, 1, 1, 1, 1, 1, 3, 4, 4]
def baseStart_2845287 : Nat := 118140960795 + 2845287 * 2 ^ 59
def prefixEnd_2845287 : Nat := 4983230072969 + 3 ^ 40 * 2845287 * 2
def baseEnd_2845287 : Nat := 1460999830989314535227269

theorem tailTrace_2845287 : CollatzResearch.WordTrace tailWord_2845287 prefixEnd_2845287 1460999830989314535227269 := by
  unfold tailWord_2845287
  simp only [CollatzResearch.WordTrace]
  refine ⟨103776142443018610177342115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69184094962012406784894743 103776142443018610177342115)
  ·
    refine ⟨155664213664527915266013173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103776142443018610177342115 155664213664527915266013173)
    ·
      refine ⟨14593520031049492056188735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 155664213664527915266013173 14593520031049492056188735)
      ·
        refine ⟨21890280046574238084283103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14593520031049492056188735 21890280046574238084283103)
        ·
          refine ⟨32835420069861357126424655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21890280046574238084283103 32835420069861357126424655)
          ·
            refine ⟨49253130104792035689636983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32835420069861357126424655 49253130104792035689636983)
            ·
              refine ⟨73879695157188053534455475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49253130104792035689636983 73879695157188053534455475)
              ·
                refine ⟨110819542735782080301683213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 73879695157188053534455475 110819542735782080301683213)
                ·
                  refine ⟨41557328525918280113131205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 110819542735782080301683213 41557328525918280113131205)
                  ·
                    refine ⟨7791999098609677521212101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 41557328525918280113131205 7791999098609677521212101)
                    ·
                      refine ⟨1460999830989314535227269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7791999098609677521212101 1460999830989314535227269)
                      ·
                        rfl

theorem cell23_2845287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 1, 3, 4, 4].length) (baseStart_2845287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2845287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2845287 prefixEnd_2845287 := by exact prefixLift 2845287
  have htrace : WordTrace (prefixWord ++ tailWord_2845287) baseStart_2845287 baseEnd_2845287 := by
    simpa [prefixWord, tailWord_2845287, baseEnd_2845287] using wordTrace_append hprefix tailTrace_2845287
  have hstable : (prefixWord ++ tailWord_2845287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2845287).length < 2 ^ (prefixWord ++ tailWord_2845287).sum := by decide
  have hdescent : baseEnd_2845287 < baseStart_2845287 := by decide
  rcases family_descends (prefixWord ++ tailWord_2845287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2845302 : List Nat := [5, 1, 1, 2, 4, 1, 1, 2, 2, 1, 3]
def baseStart_2845302 : Nat := 118140960795 + 2845302 * 2 ^ 59
def prefixEnd_2845302 : Nat := 4983230072969 + 3 ^ 40 * 2845302 * 2
def baseEnd_2845302 : Nat := 1461007533199131976539701

theorem tailTrace_2845302 : CollatzResearch.WordTrace tailWord_2845302 prefixEnd_2845302 1461007533199131976539701 := by
  unfold tailWord_2845302
  simp only [CollatzResearch.WordTrace]
  refine ⟨6486043096122766733696135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 69184459691976178492758773 6486043096122766733696135)
  ·
    refine ⟨9729064644184150100544203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6486043096122766733696135 9729064644184150100544203)
    ·
      refine ⟨14593596966276225150816305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9729064644184150100544203 14593596966276225150816305)
      ·
        refine ⟨10945197724707168863112229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14593596966276225150816305 10945197724707168863112229)
        ·
          refine ⟨2052224573382594161833543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10945197724707168863112229 2052224573382594161833543)
          ·
            refine ⟨3078336860073891242750315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2052224573382594161833543 3078336860073891242750315)
            ·
              refine ⟨4617505290110836864125473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3078336860073891242750315 4617505290110836864125473)
              ·
                refine ⟨3463128967583127648094105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4617505290110836864125473 3463128967583127648094105)
                ·
                  refine ⟨2597346725687345736070579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3463128967583127648094105 2597346725687345736070579)
                  ·
                    refine ⟨3896020088531018604105869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2597346725687345736070579 3896020088531018604105869)
                    ·
                      refine ⟨1461007533199131976539701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3896020088531018604105869 1461007533199131976539701)
                      ·
                        rfl

theorem cell23_2845302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 4, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 4, 1, 1, 2, 2, 1, 3].length) (baseStart_2845302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2845302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2845302 prefixEnd_2845302 := by exact prefixLift 2845302
  have htrace : WordTrace (prefixWord ++ tailWord_2845302) baseStart_2845302 baseEnd_2845302 := by
    simpa [prefixWord, tailWord_2845302, baseEnd_2845302] using wordTrace_append hprefix tailTrace_2845302
  have hstable : (prefixWord ++ tailWord_2845302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2845302).length < 2 ^ (prefixWord ++ tailWord_2845302).sum := by decide
  have hdescent : baseEnd_2845302 < baseStart_2845302 := by decide
  rcases family_descends (prefixWord ++ tailWord_2845302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2845308 : List Nat := [2, 2, 2, 1, 1, 2, 5, 2, 2, 2, 2]
def baseStart_2845308 : Nat := 118140960795 + 2845308 * 2 ^ 59
def prefixEnd_2845308 : Nat := 4983230072969 + 3 ^ 40 * 2845308 * 2
def baseEnd_2845308 : Nat := 1461010614083058953064673

theorem tailTrace_2845308 : CollatzResearch.WordTrace tailWord_2845308 prefixEnd_2845308 1461010614083058953064673 := by
  unfold tailWord_2845308
  simp only [CollatzResearch.WordTrace]
  refine ⟨51888454187971265381928289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69184605583961687175904385 51888454187971265381928289)
  ·
    refine ⟨38916340640978449036446217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51888454187971265381928289 38916340640978449036446217)
    ·
      refine ⟨29187255480733836777334663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38916340640978449036446217 29187255480733836777334663)
      ·
        refine ⟨43780883221100755166001995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29187255480733836777334663 43780883221100755166001995)
        ·
          refine ⟨65671324831651132749002993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43780883221100755166001995 65671324831651132749002993)
          ·
            refine ⟨49253493623738349561752245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65671324831651132749002993 49253493623738349561752245)
            ·
              refine ⟨4617515027225470271414273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 49253493623738349561752245 4617515027225470271414273)
              ·
                refine ⟨3463136270419102703560705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4617515027225470271414273 3463136270419102703560705)
                ·
                  refine ⟨2597352202814327027670529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3463136270419102703560705 2597352202814327027670529)
                  ·
                    refine ⟨1948014152110745270752897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2597352202814327027670529 1948014152110745270752897)
                    ·
                      refine ⟨1461010614083058953064673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1948014152110745270752897 1461010614083058953064673)
                      ·
                        rfl

theorem cell23_2845308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 5, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 5, 2, 2, 2, 2].length) (baseStart_2845308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2845308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2845308 prefixEnd_2845308 := by exact prefixLift 2845308
  have htrace : WordTrace (prefixWord ++ tailWord_2845308) baseStart_2845308 baseEnd_2845308 := by
    simpa [prefixWord, tailWord_2845308, baseEnd_2845308] using wordTrace_append hprefix tailTrace_2845308
  have hstable : (prefixWord ++ tailWord_2845308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2845308).length < 2 ^ (prefixWord ++ tailWord_2845308).sum := by decide
  have hdescent : baseEnd_2845308 < baseStart_2845308 := by decide
  rcases family_descends (prefixWord ++ tailWord_2845308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2845327 : List Nat := [1, 1, 2, 1, 1, 1, 1, 6, 4, 5]
def baseStart_2845327 : Nat := 118140960795 + 2845327 * 2 ^ 59
def prefixEnd_2845327 : Nat := 4983230072969 + 3 ^ 40 * 2845327 * 2
def baseEnd_2845327 : Nat := 487006790071831459575695

theorem tailTrace_2845327 : CollatzResearch.WordTrace tailWord_2845327 prefixEnd_2845327 487006790071831459575695 := by
  unfold tailWord_2845327
  simp only [CollatzResearch.WordTrace]
  refine ⟨103777601362873697008798235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69185067575249131339198823 103777601362873697008798235)
  ·
    refine ⟨155666402044310545513197353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103777601362873697008798235 155666402044310545513197353)
    ·
      refine ⟨116749801533232909134898015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 155666402044310545513197353 116749801533232909134898015)
      ·
        refine ⟨175124702299849363702347023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116749801533232909134898015 175124702299849363702347023)
        ·
          refine ⟨262687053449774045553520535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 175124702299849363702347023 262687053449774045553520535)
          ·
            refine ⟨394030580174661068330280803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 262687053449774045553520535 394030580174661068330280803)
            ·
              refine ⟨591045870261991602495421205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 394030580174661068330280803 591045870261991602495421205)
              ·
                refine ⟨27705275168530856366972869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 591045870261991602495421205 27705275168530856366972869)
                ·
                  refine ⟨5194739094099535568807413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27705275168530856366972869 5194739094099535568807413)
                  ·
                    refine ⟨487006790071831459575695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5194739094099535568807413 487006790071831459575695)
                    ·
                      rfl

theorem cell23_2845327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 6, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 6, 4, 5].length) (baseStart_2845327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2845327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2845327 prefixEnd_2845327 := by exact prefixLift 2845327
  have htrace : WordTrace (prefixWord ++ tailWord_2845327) baseStart_2845327 baseEnd_2845327 := by
    simpa [prefixWord, tailWord_2845327, baseEnd_2845327] using wordTrace_append hprefix tailTrace_2845327
  have hstable : (prefixWord ++ tailWord_2845327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2845327).length < 2 ^ (prefixWord ++ tailWord_2845327).sum := by decide
  have hdescent : baseEnd_2845327 < baseStart_2845327 := by decide
  rcases family_descends (prefixWord ++ tailWord_2845327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2845401 : List Nat := [1, 2, 1, 2, 3, 2, 4, 1, 2, 2, 3]
def baseStart_2845401 : Nat := 118140960795 + 2845401 * 2 ^ 59
def prefixEnd_2845401 : Nat := 4983230072969 + 3 ^ 40 * 2845401 * 2
def baseEnd_2845401 : Nat := 1461058367783927089201745

theorem tailTrace_2845401 : CollatzResearch.WordTrace tailWord_2845401 prefixEnd_2845401 1461058367783927089201745 := by
  unfold tailWord_2845401
  simp only [CollatzResearch.WordTrace]
  refine ⟨103780300364605607646992057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69186866909737071764661371 103780300364605607646992057)
  ·
    refine ⟨77835225273454205735244043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103780300364605607646992057 77835225273454205735244043)
    ·
      refine ⟨116752837910181308602866065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77835225273454205735244043 116752837910181308602866065)
      ·
        refine ⟨87564628432635981452149549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 116752837910181308602866065 87564628432635981452149549)
        ·
          refine ⟨32836735662238493044556081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 87564628432635981452149549 32836735662238493044556081)
          ·
            refine ⟨24627551746678869783417061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32836735662238493044556081 24627551746678869783417061)
            ·
              refine ⟨4617665952502288084390699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24627551746678869783417061 4617665952502288084390699)
              ·
                refine ⟨6926498928753432126586049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4617665952502288084390699 6926498928753432126586049)
                ·
                  refine ⟨5194874196565074094939537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6926498928753432126586049 5194874196565074094939537)
                  ·
                    refine ⟨3896155647423805571204653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5194874196565074094939537 3896155647423805571204653)
                    ·
                      refine ⟨1461058367783927089201745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3896155647423805571204653 1461058367783927089201745)
                      ·
                        rfl

theorem cell23_2845401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 4, 1, 2, 2, 3].length) (baseStart_2845401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2845401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2845401 prefixEnd_2845401 := by exact prefixLift 2845401
  have htrace : WordTrace (prefixWord ++ tailWord_2845401) baseStart_2845401 baseEnd_2845401 := by
    simpa [prefixWord, tailWord_2845401, baseEnd_2845401] using wordTrace_append hprefix tailTrace_2845401
  have hstable : (prefixWord ++ tailWord_2845401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2845401).length < 2 ^ (prefixWord ++ tailWord_2845401).sum := by decide
  have hdescent : baseEnd_2845401 < baseStart_2845401 := by decide
  rcases family_descends (prefixWord ++ tailWord_2845401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2845421 : List Nat := [1, 5, 1, 2, 1, 1, 4, 2, 6]
def baseStart_2845421 : Nat := 118140960795 + 2845421 * 2 ^ 59
def prefixEnd_2845421 : Nat := 4983230072969 + 3 ^ 40 * 2845421 * 2
def baseEnd_2845421 : Nat := 162340959710779667883517

theorem tailTrace_2845421 : CollatzResearch.WordTrace tailWord_2845421 prefixEnd_2845421 162340959710779667883517 := by
  unfold tailWord_2845421
  simp only [CollatzResearch.WordTrace]
  refine ⟨103781029824533151062720117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69187353216355434041813411 103781029824533151062720117)
  ·
    refine ⟨9729471546049982912130011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 103781029824533151062720117 9729471546049982912130011)
    ·
      refine ⟨14594207319074974368195017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9729471546049982912130011 14594207319074974368195017)
      ·
        refine ⟨10945655489306230776146263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14594207319074974368195017 10945655489306230776146263)
        ·
          refine ⟨16418483233959346164219395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10945655489306230776146263 16418483233959346164219395)
          ·
            refine ⟨24627724850939019246329093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16418483233959346164219395 24627724850939019246329093)
            ·
              refine ⟨4617698409551066108686705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24627724850939019246329093 4617698409551066108686705)
              ·
                refine ⟨3463273807163299581515029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4617698409551066108686705 3463273807163299581515029)
                ·
                  refine ⟨162340959710779667883517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3463273807163299581515029 162340959710779667883517)
                  ·
                    rfl

theorem cell23_2845421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 4, 2, 6].length) (baseStart_2845421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2845421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2845421 prefixEnd_2845421 := by exact prefixLift 2845421
  have htrace : WordTrace (prefixWord ++ tailWord_2845421) baseStart_2845421 baseEnd_2845421 := by
    simpa [prefixWord, tailWord_2845421, baseEnd_2845421] using wordTrace_append hprefix tailTrace_2845421
  have hstable : (prefixWord ++ tailWord_2845421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2845421).length < 2 ^ (prefixWord ++ tailWord_2845421).sum := by decide
  have hdescent : baseEnd_2845421 < baseStart_2845421 := by decide
  rcases family_descends (prefixWord ++ tailWord_2845421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2845431 : List Nat := [1, 1, 3, 1, 1, 1, 3, 5, 3, 1, 3]
def baseStart_2845431 : Nat := 118140960795 + 2845431 * 2 ^ 59
def prefixEnd_2845431 : Nat := 4983230072969 + 3 ^ 40 * 2845431 * 2
def baseEnd_2845431 : Nat := 1461073772203561971826607

theorem tailTrace_2845431 : CollatzResearch.WordTrace tailWord_2845431 prefixEnd_2845431 1461073772203561971826607 := by
  unfold tailWord_2845431
  simp only [CollatzResearch.WordTrace]
  refine ⟨103781394554496922770584147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69187596369664615180389431 103781394554496922770584147)
  ·
    refine ⟨155672091831745384155876221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103781394554496922770584147 155672091831745384155876221)
    ·
      refine ⟨58377034436904519058453583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 155672091831745384155876221 58377034436904519058453583)
      ·
        refine ⟨87565551655356778587680375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58377034436904519058453583 87565551655356778587680375)
        ·
          refine ⟨131348327483035167881520563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87565551655356778587680375 131348327483035167881520563)
          ·
            refine ⟨197022491224552751822280845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 131348327483035167881520563 197022491224552751822280845)
            ·
              refine ⟨73883434209207281933355317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 197022491224552751822280845 73883434209207281933355317)
              ·
                refine ⟨6926571957113182681252061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 73883434209207281933355317 6926571957113182681252061)
                ·
                  refine ⟨2597464483917443505469523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6926571957113182681252061 2597464483917443505469523)
                  ·
                    refine ⟨3896196725876165258204285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2597464483917443505469523 3896196725876165258204285)
                    ·
                      refine ⟨1461073772203561971826607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3896196725876165258204285 1461073772203561971826607)
                      ·
                        rfl

theorem cell23_2845431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 5, 3, 1, 3].length) (baseStart_2845431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2845431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2845431 prefixEnd_2845431 := by exact prefixLift 2845431
  have htrace : WordTrace (prefixWord ++ tailWord_2845431) baseStart_2845431 baseEnd_2845431 := by
    simpa [prefixWord, tailWord_2845431, baseEnd_2845431] using wordTrace_append hprefix tailTrace_2845431
  have hstable : (prefixWord ++ tailWord_2845431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2845431).length < 2 ^ (prefixWord ++ tailWord_2845431).sum := by decide
  have hdescent : baseEnd_2845431 < baseStart_2845431 := by decide
  rcases family_descends (prefixWord ++ tailWord_2845431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2845434 : List Nat := [3, 1, 1, 1, 1, 3, 3, 2, 3, 5]
def baseStart_2845434 : Nat := 118140960795 + 2845434 * 2 ^ 59
def prefixEnd_2845434 : Nat := 4983230072969 + 3 ^ 40 * 2845434 * 2
def baseEnd_2845434 : Nat := 487025104215175153363031

theorem tailTrace_2845434 : CollatzResearch.WordTrace tailWord_2845434 prefixEnd_2845434 487025104215175153363031 := by
  unfold tailWord_2845434
  simp only [CollatzResearch.WordTrace]
  refine ⟨25945375993371513570735839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69187669315657369521962237 25945375993371513570735839)
  ·
    refine ⟨38918063990057270356103759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25945375993371513570735839 38918063990057270356103759)
    ·
      refine ⟨58377095985085905534155639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38918063990057270356103759 58377095985085905534155639)
      ·
        refine ⟨87565643977628858301233459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58377095985085905534155639 87565643977628858301233459)
        ·
          refine ⟨131348465966443287451850189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87565643977628858301233459 131348465966443287451850189)
          ·
            refine ⟨49255674737416232794443821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 131348465966443287451850189 49255674737416232794443821)
            ·
              refine ⟨18470878026531087297916433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49255674737416232794443821 18470878026531087297916433)
              ·
                refine ⟨13853158519898315473437325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18470878026531087297916433 13853158519898315473437325)
                ·
                  refine ⟨5194934444961868302538997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13853158519898315473437325 5194934444961868302538997)
                  ·
                    refine ⟨487025104215175153363031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5194934444961868302538997 487025104215175153363031)
                    ·
                      rfl

theorem cell23_2845434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 3, 2, 3, 5].length) (baseStart_2845434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2845434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2845434 prefixEnd_2845434 := by exact prefixLift 2845434
  have htrace : WordTrace (prefixWord ++ tailWord_2845434) baseStart_2845434 baseEnd_2845434 := by
    simpa [prefixWord, tailWord_2845434, baseEnd_2845434] using wordTrace_append hprefix tailTrace_2845434
  have hstable : (prefixWord ++ tailWord_2845434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2845434).length < 2 ^ (prefixWord ++ tailWord_2845434).sum := by decide
  have hdescent : baseEnd_2845434 < baseStart_2845434 := by decide
  rcases family_descends (prefixWord ++ tailWord_2845434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2845441 : List Nat := [1, 2, 4, 1, 1, 1, 1, 4, 1, 5, 2]
def baseStart_2845441 : Nat := 118140960795 + 2845441 * 2 ^ 59
def prefixEnd_2845441 : Nat := 4983230072969 + 3 ^ 40 * 2845441 * 2
def baseEnd_2845441 : Nat := 1461078907010106932701561

theorem tailTrace_2845441 : CollatzResearch.WordTrace tailWord_2845441 prefixEnd_2845441 1461078907010106932701561 := by
  unfold tailWord_2845441
  simp only [CollatzResearch.WordTrace]
  refine ⟨103781759284460694478448177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69187839522973796318965451 103781759284460694478448177)
  ·
    refine ⟨77836319463345520858836133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103781759284460694478448177 77836319463345520858836133)
    ·
      refine ⟨14594309899377285161031775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 77836319463345520858836133 14594309899377285161031775)
      ·
        refine ⟨21891464849065927741547663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14594309899377285161031775 21891464849065927741547663)
        ·
          refine ⟨32837197273598891612321495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21891464849065927741547663 32837197273598891612321495)
          ·
            refine ⟨49255795910398337418482243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32837197273598891612321495 49255795910398337418482243)
            ·
              refine ⟨73883693865597506127723365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49255795910398337418482243 73883693865597506127723365)
              ·
                refine ⟨13853192599799532398948131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 73883693865597506127723365 13853192599799532398948131)
                ·
                  refine ⟨20779788899699298598422197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13853192599799532398948131 20779788899699298598422197)
                  ·
                    refine ⟨1948105209346809243602081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 20779788899699298598422197 1948105209346809243602081)
                    ·
                      refine ⟨1461078907010106932701561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1948105209346809243602081 1461078907010106932701561)
                      ·
                        rfl

theorem cell23_2845441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 4, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 4, 1, 5, 2].length) (baseStart_2845441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2845441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2845441 prefixEnd_2845441 := by exact prefixLift 2845441
  have htrace : WordTrace (prefixWord ++ tailWord_2845441) baseStart_2845441 baseEnd_2845441 := by
    simpa [prefixWord, tailWord_2845441, baseEnd_2845441] using wordTrace_append hprefix tailTrace_2845441
  have hstable : (prefixWord ++ tailWord_2845441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2845441).length < 2 ^ (prefixWord ++ tailWord_2845441).sum := by decide
  have hdescent : baseEnd_2845441 < baseStart_2845441 := by decide
  rcases family_descends (prefixWord ++ tailWord_2845441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2845444 : List Nat := [2, 3, 2, 2, 1, 1, 1, 1, 2, 1, 7]
def baseStart_2845444 : Nat := 118140960795 + 2845444 * 2 ^ 59
def prefixEnd_2845444 : Nat := 4983230072969 + 3 ^ 40 * 2845444 * 2
def baseEnd_2845444 : Nat := 1461080447452070420964047

theorem tailTrace_2845444 : CollatzResearch.WordTrace tailWord_2845444 prefixEnd_2845444 1461080447452070420964047 := by
  unfold tailWord_2845444
  simp only [CollatzResearch.WordTrace]
  refine ⟨51890934351724912995403693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69187912468966550660538257 51890934351724912995403693)
  ·
    refine ⟨19459100381896842373276385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51890934351724912995403693 19459100381896842373276385)
    ·
      refine ⟨14594325286422631779957289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19459100381896842373276385 14594325286422631779957289)
      ·
        refine ⟨10945743964816973834967967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14594325286422631779957289 10945743964816973834967967)
        ·
          refine ⟨16418615947225460752451951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10945743964816973834967967 16418615947225460752451951)
          ·
            refine ⟨24627923920838191128677927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16418615947225460752451951 24627923920838191128677927)
            ·
              refine ⟨36941885881257286693016891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24627923920838191128677927 36941885881257286693016891)
              ·
                refine ⟨55412828821885930039525337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36941885881257286693016891 55412828821885930039525337)
                ·
                  refine ⟨41559621616414447529644003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 55412828821885930039525337 41559621616414447529644003)
                  ·
                    refine ⟨62339432424621671294466005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 41559621616414447529644003 62339432424621671294466005)
                    ·
                      refine ⟨1461080447452070420964047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 62339432424621671294466005 1461080447452070420964047)
                      ·
                        rfl

theorem cell23_2845444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 1, 2, 1, 7].length) (baseStart_2845444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2845444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2845444 prefixEnd_2845444 := by exact prefixLift 2845444
  have htrace : WordTrace (prefixWord ++ tailWord_2845444) baseStart_2845444 baseEnd_2845444 := by
    simpa [prefixWord, tailWord_2845444, baseEnd_2845444] using wordTrace_append hprefix tailTrace_2845444
  have hstable : (prefixWord ++ tailWord_2845444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2845444).length < 2 ^ (prefixWord ++ tailWord_2845444).sum := by decide
  have hdescent : baseEnd_2845444 < baseStart_2845444 := by decide
  rcases family_descends (prefixWord ++ tailWord_2845444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2845448 : List Nat := [2, 1, 3, 2, 2, 3, 1, 2, 3, 1, 3]
def baseStart_2845448 : Nat := 118140960795 + 2845448 * 2 ^ 59
def prefixEnd_2845448 : Nat := 4983230072969 + 3 ^ 40 * 2845448 * 2
def baseEnd_2845448 : Nat := 1461082501374688405314029

theorem tailTrace_2845448 : CollatzResearch.WordTrace tailWord_2845448 prefixEnd_2845448 1461082501374688405314029 := by
  unfold tailWord_2845448
  simp only [CollatzResearch.WordTrace]
  refine ⟨51891007297717667336976499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69188009730290223115968665 51891007297717667336976499)
  ·
    refine ⟨77836510946576501005464749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51891007297717667336976499 77836510946576501005464749)
    ·
      refine ⟨29188691604966187877049281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 77836510946576501005464749 29188691604966187877049281)
      ·
        refine ⟨21891518703724640907786961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29188691604966187877049281 21891518703724640907786961)
        ·
          refine ⟨16418639027793480680840221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21891518703724640907786961 16418639027793480680840221)
          ·
            refine ⟨6156989635422555255315083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16418639027793480680840221 6156989635422555255315083)
            ·
              refine ⟨9235484453133832882972625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6156989635422555255315083 9235484453133832882972625)
              ·
                refine ⟨6926613339850374662229469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9235484453133832882972625 6926613339850374662229469)
                ·
                  refine ⟨2597480002443890498336051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6926613339850374662229469 2597480002443890498336051)
                  ·
                    refine ⟨3896220003665835747504077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2597480002443890498336051 3896220003665835747504077)
                    ·
                      refine ⟨1461082501374688405314029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3896220003665835747504077 1461082501374688405314029)
                      ·
                        rfl

theorem cell23_2845448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 1, 2, 3, 1, 3].length) (baseStart_2845448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2845448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2845448 prefixEnd_2845448 := by exact prefixLift 2845448
  have htrace : WordTrace (prefixWord ++ tailWord_2845448) baseStart_2845448 baseEnd_2845448 := by
    simpa [prefixWord, tailWord_2845448, baseEnd_2845448] using wordTrace_append hprefix tailTrace_2845448
  have hstable : (prefixWord ++ tailWord_2845448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2845448).length < 2 ^ (prefixWord ++ tailWord_2845448).sum := by decide
  have hdescent : baseEnd_2845448 < baseStart_2845448 := by decide
  rcases family_descends (prefixWord ++ tailWord_2845448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2845468 : List Nat := [2, 2, 3, 1, 1, 3, 4, 1, 1, 5]
def baseStart_2845468 : Nat := 118140960795 + 2845468 * 2 ^ 59
def prefixEnd_2845468 : Nat := 4983230072969 + 3 ^ 40 * 2845468 * 2
def baseEnd_2845468 : Nat := 487030923662592775687979

theorem tailTrace_2845468 : CollatzResearch.WordTrace tailWord_2845468 prefixEnd_2845468 487030923662592775687979 := by
  unfold tailWord_2845468
  simp only [CollatzResearch.WordTrace]
  refine ⟨51891372027681439044840529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69188496036908585393120705 51891372027681439044840529)
  ·
    refine ⟨38918529020761079283630397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51891372027681439044840529 38918529020761079283630397)
    ·
      refine ⟨14594448382785404731361399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38918529020761079283630397 14594448382785404731361399)
      ·
        refine ⟨21891672574178107097042099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14594448382785404731361399 21891672574178107097042099)
        ·
          refine ⟨32837508861267160645563149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21891672574178107097042099 32837508861267160645563149)
          ·
            refine ⟨12314065822975185242086181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32837508861267160645563149 12314065822975185242086181)
            ·
              refine ⟨2308887341807847232891159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12314065822975185242086181 2308887341807847232891159)
              ·
                refine ⟨3463331012711770849336739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2308887341807847232891159 3463331012711770849336739)
                ·
                  refine ⟨5194996519067656274005109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3463331012711770849336739 5194996519067656274005109)
                  ·
                    refine ⟨487030923662592775687979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5194996519067656274005109 487030923662592775687979)
                    ·
                      rfl

theorem cell23_2845468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 4, 1, 1, 5].length) (baseStart_2845468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2845468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2845468 prefixEnd_2845468 := by exact prefixLift 2845468
  have htrace : WordTrace (prefixWord ++ tailWord_2845468) baseStart_2845468 baseEnd_2845468 := by
    simpa [prefixWord, tailWord_2845468, baseEnd_2845468] using wordTrace_append hprefix tailTrace_2845468
  have hstable : (prefixWord ++ tailWord_2845468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2845468).length < 2 ^ (prefixWord ++ tailWord_2845468).sum := by decide
  have hdescent : baseEnd_2845468 < baseStart_2845468 := by decide
  rcases family_descends (prefixWord ++ tailWord_2845468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2845482 : List Nat := [3, 1, 4, 3, 1, 1, 2, 1, 3, 1, 3]
def baseStart_2845482 : Nat := 118140960795 + 2845482 * 2 ^ 59
def prefixEnd_2845482 : Nat := 4983230072969 + 3 ^ 40 * 2845482 * 2
def baseEnd_2845482 : Nat := 1461099959716941272288873

theorem tailTrace_2845482 : CollatzResearch.WordTrace tailWord_2845482 prefixEnd_2845482 1461099959716941272288873 := by
  unfold tailWord_2845482
  simp only [CollatzResearch.WordTrace]
  refine ⟨25945813669328039620172675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69188836451541438987127133 25945813669328039620172675)
  ·
    refine ⟨38918720503992059430259013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25945813669328039620172675 38918720503992059430259013)
    ·
      refine ⟨7297260094498511143173565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 38918720503992059430259013 7297260094498511143173565)
      ·
        refine ⟨2736472535436941678690087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7297260094498511143173565 2736472535436941678690087)
        ·
          refine ⟨4104708803155412518035131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2736472535436941678690087 4104708803155412518035131)
          ·
            refine ⟨6157063204733118777052697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4104708803155412518035131 6157063204733118777052697)
            ·
              refine ⟨4617797403549839082789523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6157063204733118777052697 4617797403549839082789523)
              ·
                refine ⟨6926696105324758624184285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4617797403549839082789523 6926696105324758624184285)
                ·
                  refine ⟨2597511039496784484069107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6926696105324758624184285 2597511039496784484069107)
                  ·
                    refine ⟨3896266559245176726103661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2597511039496784484069107 3896266559245176726103661)
                    ·
                      refine ⟨1461099959716941272288873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3896266559245176726103661 1461099959716941272288873)
                      ·
                        rfl

theorem cell23_2845482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 2, 1, 3, 1, 3].length) (baseStart_2845482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2845482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2845482 prefixEnd_2845482 := by exact prefixLift 2845482
  have htrace : WordTrace (prefixWord ++ tailWord_2845482) baseStart_2845482 baseEnd_2845482 := by
    simpa [prefixWord, tailWord_2845482, baseEnd_2845482] using wordTrace_append hprefix tailTrace_2845482
  have hstable : (prefixWord ++ tailWord_2845482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2845482).length < 2 ^ (prefixWord ++ tailWord_2845482).sum := by decide
  have hdescent : baseEnd_2845482 < baseStart_2845482 := by decide
  rcases family_descends (prefixWord ++ tailWord_2845482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2845484 : List Nat := [2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 6]
def baseStart_2845484 : Nat := 118140960795 + 2845484 * 2 ^ 59
def prefixEnd_2845484 : Nat := 4983230072969 + 3 ^ 40 * 2845484 * 2
def baseEnd_2845484 : Nat := 1461100986678250264463863

theorem tailTrace_2845484 : CollatzResearch.WordTrace tailWord_2845484 prefixEnd_2845484 1461100986678250264463863 := by
  unfold tailWord_2845484
  simp only [CollatzResearch.WordTrace]
  refine ⟨51891663811652456411131753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69188885082203275214842337 51891663811652456411131753)
  ·
    refine ⟨38918747858739342308348815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51891663811652456411131753 38918747858739342308348815)
    ·
      refine ⟨58378121788109013462523223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38918747858739342308348815 58378121788109013462523223)
      ·
        refine ⟨87567182682163520193784835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58378121788109013462523223 87567182682163520193784835)
        ·
          refine ⟨131350774023245280290677253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87567182682163520193784835 131350774023245280290677253)
          ·
            refine ⟨24628270129358490054501985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 131350774023245280290677253 24628270129358490054501985)
            ·
              refine ⟨18471202597018867540876489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24628270129358490054501985 18471202597018867540876489)
              ·
                refine ⟨13853401947764150655657367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18471202597018867540876489 13853401947764150655657367)
                ·
                  refine ⟨20780102921646225983486051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13853401947764150655657367 20780102921646225983486051)
                  ·
                    refine ⟨31170154382469338975229077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20780102921646225983486051 31170154382469338975229077)
                    ·
                      refine ⟨1461100986678250264463863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 31170154382469338975229077 1461100986678250264463863)
                      ·
                        rfl

theorem cell23_2845484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 6].length) (baseStart_2845484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2845484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2845484 prefixEnd_2845484 := by exact prefixLift 2845484
  have htrace : WordTrace (prefixWord ++ tailWord_2845484) baseStart_2845484 baseEnd_2845484 := by
    simpa [prefixWord, tailWord_2845484, baseEnd_2845484] using wordTrace_append hprefix tailTrace_2845484
  have hstable : (prefixWord ++ tailWord_2845484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2845484).length < 2 ^ (prefixWord ++ tailWord_2845484).sum := by decide
  have hdescent : baseEnd_2845484 < baseStart_2845484 := by decide
  rcases family_descends (prefixWord ++ tailWord_2845484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2845491 : List Nat := [1, 1, 1, 2, 6, 2, 1, 2, 1, 1, 5]
def baseStart_2845491 : Nat := 118140960795 + 2845491 * 2 ^ 59
def prefixEnd_2845491 : Nat := 4983230072969 + 3 ^ 40 * 2845491 * 2
def baseEnd_2845491 : Nat := 1461104581042831737076331

theorem tailTrace_2845491 : CollatzResearch.WordTrace tailWord_2845491 prefixEnd_2845491 1461104581042831737076331 := by
  unfold tailWord_2845491
  simp only [CollatzResearch.WordTrace]
  refine ⟨103783582934279553017768327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69189055289519702011845551 103783582934279553017768327)
  ·
    refine ⟨155675374401419329526652491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103783582934279553017768327 155675374401419329526652491)
    ·
      refine ⟨233513061602128994289978737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155675374401419329526652491 233513061602128994289978737)
      ·
        refine ⟨175134796201596745717484053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 233513061602128994289978737 175134796201596745717484053)
        ·
          refine ⟨8209443571949847455507065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 175134796201596745717484053 8209443571949847455507065)
          ·
            refine ⟨6157082678962385591630299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8209443571949847455507065 6157082678962385591630299)
            ·
              refine ⟨9235624018443578387445449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6157082678962385591630299 9235624018443578387445449)
              ·
                refine ⟨6926718013832683790584087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9235624018443578387445449 6926718013832683790584087)
                ·
                  refine ⟨10390077020749025685876131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6926718013832683790584087 10390077020749025685876131)
                  ·
                    refine ⟨15585115531123538528814197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10390077020749025685876131 15585115531123538528814197)
                    ·
                      refine ⟨1461104581042831737076331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15585115531123538528814197 1461104581042831737076331)
                      ·
                        rfl

theorem cell23_2845491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 1, 2, 1, 1, 5].length) (baseStart_2845491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2845491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2845491 prefixEnd_2845491 := by exact prefixLift 2845491
  have htrace : WordTrace (prefixWord ++ tailWord_2845491) baseStart_2845491 baseEnd_2845491 := by
    simpa [prefixWord, tailWord_2845491, baseEnd_2845491] using wordTrace_append hprefix tailTrace_2845491
  have hstable : (prefixWord ++ tailWord_2845491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2845491).length < 2 ^ (prefixWord ++ tailWord_2845491).sum := by decide
  have hdescent : baseEnd_2845491 < baseStart_2845491 := by decide
  rcases family_descends (prefixWord ++ tailWord_2845491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2845498 : List Nat := [3, 1, 1, 1, 6, 2, 1, 1, 1, 6]
def baseStart_2845498 : Nat := 118140960795 + 2845498 * 2 ^ 59
def prefixEnd_2845498 : Nat := 4983230072969 + 3 ^ 40 * 2845498 * 2
def baseEnd_2845498 : Nat := 487036058469137736562933

theorem tailTrace_2845498 : CollatzResearch.WordTrace tailWord_2845498 prefixEnd_2845498 487036058469137736562933 := by
  unfold tailWord_2845498
  simp only [CollatzResearch.WordTrace]
  refine ⟨25945959561313548303318287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69189225496836128808848765 25945959561313548303318287)
  ·
    refine ⟨38918939341970322454977431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25945959561313548303318287 38918939341970322454977431)
    ·
      refine ⟨58378409012955483682466147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38918939341970322454977431 58378409012955483682466147)
      ·
        refine ⟨87567613519433225523699221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58378409012955483682466147 87567613519433225523699221)
        ·
          refine ⟨4104731883723432446423401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 87567613519433225523699221 4104731883723432446423401)
          ·
            refine ⟨3078548912792574334817551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4104731883723432446423401 3078548912792574334817551)
            ·
              refine ⟨4617823369188861502226327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3078548912792574334817551 4617823369188861502226327)
              ·
                refine ⟨6926735053783292253339491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4617823369188861502226327 6926735053783292253339491)
                ·
                  refine ⟨10390102580674938380009237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6926735053783292253339491 10390102580674938380009237)
                  ·
                    refine ⟨487036058469137736562933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10390102580674938380009237 487036058469137736562933)
                    ·
                      rfl

theorem cell23_2845498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 2, 1, 1, 1, 6].length) (baseStart_2845498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2845498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2845498 prefixEnd_2845498 := by exact prefixLift 2845498
  have htrace : WordTrace (prefixWord ++ tailWord_2845498) baseStart_2845498 baseEnd_2845498 := by
    simpa [prefixWord, tailWord_2845498, baseEnd_2845498] using wordTrace_append hprefix tailTrace_2845498
  have hstable : (prefixWord ++ tailWord_2845498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2845498).length < 2 ^ (prefixWord ++ tailWord_2845498).sum := by decide
  have hdescent : baseEnd_2845498 < baseStart_2845498 := by decide
  rcases family_descends (prefixWord ++ tailWord_2845498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2845539 : List Nat := [1, 1, 1, 5, 3, 2, 3, 2, 1, 2, 2]
def baseStart_2845539 : Nat := 118140960795 + 2845539 * 2 ^ 59
def prefixEnd_2845539 : Nat := 4983230072969 + 3 ^ 40 * 2845539 * 2
def baseEnd_2845539 : Nat := 1461129228114247549276111

theorem tailTrace_2845539 : CollatzResearch.WordTrace tailWord_2845539 prefixEnd_2845539 1461129228114247549276111 := by
  unfold tailWord_2845539
  simp only [CollatzResearch.WordTrace]
  refine ⟨103785333638105657215515671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69190222425403771477010447 103785333638105657215515671)
  ·
    refine ⟨155678000457158485823273507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103785333638105657215515671 155678000457158485823273507)
    ·
      refine ⟨233517000685737728734910261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155678000457158485823273507 233517000685737728734910261)
      ·
        refine ⟨21892218814287912068897837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 233517000685737728734910261 21892218814287912068897837)
        ·
          refine ⟨8209582055357967025836689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21892218814287912068897837 8209582055357967025836689)
          ·
            refine ⟨6157186541518475269377517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8209582055357967025836689 6157186541518475269377517)
            ·
              refine ⟨2308944953069428226016569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6157186541518475269377517 2308944953069428226016569)
              ·
                refine ⟨1731708714802071169512427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2308944953069428226016569 1731708714802071169512427)
                ·
                  refine ⟨2597563072203106754268641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1731708714802071169512427 2597563072203106754268641)
                  ·
                    refine ⟨1948172304152330065701481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2597563072203106754268641 1948172304152330065701481)
                    ·
                      refine ⟨1461129228114247549276111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1948172304152330065701481 1461129228114247549276111)
                      ·
                        rfl

theorem cell23_2845539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 3, 2, 1, 2, 2].length) (baseStart_2845539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2845539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2845539 prefixEnd_2845539 := by exact prefixLift 2845539
  have htrace : WordTrace (prefixWord ++ tailWord_2845539) baseStart_2845539 baseEnd_2845539 := by
    simpa [prefixWord, tailWord_2845539, baseEnd_2845539] using wordTrace_append hprefix tailTrace_2845539
  have hstable : (prefixWord ++ tailWord_2845539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2845539).length < 2 ^ (prefixWord ++ tailWord_2845539).sum := by decide
  have hdescent : baseEnd_2845539 < baseStart_2845539 := by decide
  rcases family_descends (prefixWord ++ tailWord_2845539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2845548 : List Nat := [2, 2, 1, 1, 4, 1, 2, 2, 3, 3, 2]
def baseStart_2845548 : Nat := 118140960795 + 2845548 * 2 ^ 59
def prefixEnd_2845548 : Nat := 4983230072969 + 3 ^ 40 * 2845548 * 2
def baseEnd_2845548 : Nat := 1461133849440138014063569

theorem tailTrace_2845548 : CollatzResearch.WordTrace tailWord_2845548 prefixEnd_2845548 1461133849440138014063569 := by
  unfold tailWord_2845548
  simp only [CollatzResearch.WordTrace]
  refine ⟨51892830947536525876296649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69190441263382034501728865 51892830947536525876296649)
  ·
    refine ⟨38919623210652394407222487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51892830947536525876296649 38919623210652394407222487)
    ·
      refine ⟨58379434815978591610833731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38919623210652394407222487 58379434815978591610833731)
      ·
        refine ⟨87569152223967887416250597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58379434815978591610833731 87569152223967887416250597)
        ·
          refine ⟨16419216041993978890546987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 87569152223967887416250597 16419216041993978890546987)
          ·
            refine ⟨24628824062990968335820481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16419216041993978890546987 24628824062990968335820481)
            ·
              refine ⟨18471618047243226251865361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24628824062990968335820481 18471618047243226251865361)
              ·
                refine ⟨13853713535432419688899021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18471618047243226251865361 13853713535432419688899021)
                ·
                  refine ⟨5195142575787157383337133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13853713535432419688899021 5195142575787157383337133)
                  ·
                    refine ⟨1948178465920184018751425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5195142575787157383337133 1948178465920184018751425)
                    ·
                      refine ⟨1461133849440138014063569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1948178465920184018751425 1461133849440138014063569)
                      ·
                        rfl

theorem cell23_2845548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 3, 2].length) (baseStart_2845548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2845548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2845548 prefixEnd_2845548 := by exact prefixLift 2845548
  have htrace : WordTrace (prefixWord ++ tailWord_2845548) baseStart_2845548 baseEnd_2845548 := by
    simpa [prefixWord, tailWord_2845548, baseEnd_2845548] using wordTrace_append hprefix tailTrace_2845548
  have hstable : (prefixWord ++ tailWord_2845548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2845548).length < 2 ^ (prefixWord ++ tailWord_2845548).sum := by decide
  have hdescent : baseEnd_2845548 < baseStart_2845548 := by decide
  rcases family_descends (prefixWord ++ tailWord_2845548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2845555 : List Nat := [1, 1, 1, 2, 2, 1, 8, 1, 2, 1, 3]
def baseStart_2845555 : Nat := 118140960795 + 2845555 * 2 ^ 59
def prefixEnd_2845555 : Nat := 4983230072969 + 3 ^ 40 * 2845555 * 2
def baseEnd_2845555 : Nat := 1461137443804719486676037

theorem tailTrace_2845555 : CollatzResearch.WordTrace tailWord_2845555 prefixEnd_2845555 1461137443804719486676037 := by
  unfold tailWord_2845555
  simp only [CollatzResearch.WordTrace]
  refine ⟨103785917206047691948098119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69190611470698461298732079 103785917206047691948098119)
  ·
    refine ⟨155678875809071537922147179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103785917206047691948098119 155678875809071537922147179)
    ·
      refine ⟨233518313713607306883220769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155678875809071537922147179 233518313713607306883220769)
      ·
        refine ⟨175138735285205480162415577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 233518313713607306883220769 175138735285205480162415577)
        ·
          refine ⟨131354051463904110121811683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 175138735285205480162415577 131354051463904110121811683)
          ·
            refine ⟨197031077195856165182717525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 131354051463904110121811683 197031077195856165182717525)
            ·
              refine ⟨2308957935888939435734971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 197031077195856165182717525 2308957935888939435734971)
              ·
                refine ⟨3463436903833409153602457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2308957935888939435734971 3463436903833409153602457)
                ·
                  refine ⟨2597577677875056865201843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3463436903833409153602457 2597577677875056865201843)
                  ·
                    refine ⟨3896366516812585297802765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2597577677875056865201843 3896366516812585297802765)
                    ·
                      refine ⟨1461137443804719486676037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3896366516812585297802765 1461137443804719486676037)
                      ·
                        rfl

theorem cell23_2845555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 8, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 8, 1, 2, 1, 3].length) (baseStart_2845555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2845555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2845555 prefixEnd_2845555 := by exact prefixLift 2845555
  have htrace : WordTrace (prefixWord ++ tailWord_2845555) baseStart_2845555 baseEnd_2845555 := by
    simpa [prefixWord, tailWord_2845555, baseEnd_2845555] using wordTrace_append hprefix tailTrace_2845555
  have hstable : (prefixWord ++ tailWord_2845555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2845555).length < 2 ^ (prefixWord ++ tailWord_2845555).sum := by decide
  have hdescent : baseEnd_2845555 < baseStart_2845555 := by decide
  rcases family_descends (prefixWord ++ tailWord_2845555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2845565 : List Nat := [1, 4, 1, 1, 2, 1, 5, 2, 1, 3, 2]
def baseStart_2845565 : Nat := 118140960795 + 2845565 * 2 ^ 59
def prefixEnd_2845565 : Nat := 4983230072969 + 3 ^ 40 * 2845565 * 2
def baseEnd_2845565 : Nat := 1461142578611264447550991

theorem tailTrace_2845565 : CollatzResearch.WordTrace tailWord_2845565 prefixEnd_2845565 1461142578611264447550991 := by
  unfold tailWord_2845565
  simp only [CollatzResearch.WordTrace]
  refine ⟨103786281936011463655962149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69190854624007642437308099 103786281936011463655962149)
  ·
    refine ⟨19459927863002149435492903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 103786281936011463655962149 19459927863002149435492903)
    ·
      refine ⟨29189891794503224153239355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19459927863002149435492903 29189891794503224153239355)
      ·
        refine ⟨43784837691754836229859033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29189891794503224153239355 43784837691754836229859033)
        ·
          refine ⟨32838628268816127172394275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43784837691754836229859033 32838628268816127172394275)
          ·
            refine ⟨49257942403224190758591413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32838628268816127172394275 49257942403224190758591413)
            ·
              refine ⟨4617932100302267883617945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 49257942403224190758591413 4617932100302267883617945)
              ·
                refine ⟨3463449075226700912713459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4617932100302267883617945 3463449075226700912713459)
                ·
                  refine ⟨5195173612840051369070189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3463449075226700912713459 5195173612840051369070189)
                  ·
                    refine ⟨1948190104815019263401321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5195173612840051369070189 1948190104815019263401321)
                    ·
                      refine ⟨1461142578611264447550991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1948190104815019263401321 1461142578611264447550991)
                      ·
                        rfl

theorem cell23_2845565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 5, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 5, 2, 1, 3, 2].length) (baseStart_2845565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2845565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2845565 prefixEnd_2845565 := by exact prefixLift 2845565
  have htrace : WordTrace (prefixWord ++ tailWord_2845565) baseStart_2845565 baseEnd_2845565 := by
    simpa [prefixWord, tailWord_2845565, baseEnd_2845565] using wordTrace_append hprefix tailTrace_2845565
  have hstable : (prefixWord ++ tailWord_2845565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2845565).length < 2 ^ (prefixWord ++ tailWord_2845565).sum := by decide
  have hdescent : baseEnd_2845565 < baseStart_2845565 := by decide
  rcases family_descends (prefixWord ++ tailWord_2845565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2845590 : List Nat := [5, 3, 1, 1, 1, 3, 2, 2, 1, 2, 2]
def baseStart_2845590 : Nat := 118140960795 + 2845590 * 2 ^ 59
def prefixEnd_2845590 : Nat := 4983230072969 + 3 ^ 40 * 2845590 * 2
def baseEnd_2845590 : Nat := 1461155415627626849738377

theorem tailTrace_2845590 : CollatzResearch.WordTrace tailWord_2845590 prefixEnd_2845590 1461155415627626849738377 := by
  unfold tailWord_2845590
  simp only [CollatzResearch.WordTrace]
  refine ⟨6486699610057555807851389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 69191462507280595283748149 6486699610057555807851389)
  ·
    refine ⟨2432512353771583427944271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6486699610057555807851389 2432512353771583427944271)
    ·
      refine ⟨3648768530657375141916407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2432512353771583427944271 3648768530657375141916407)
      ·
        refine ⟨5473152795986062712874611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3648768530657375141916407 5473152795986062712874611)
        ·
          refine ⟨8209729193979094069311917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5473152795986062712874611 8209729193979094069311917)
          ·
            refine ⟨3078648447742160275991969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8209729193979094069311917 3078648447742160275991969)
            ·
              refine ⟨2308986335806620206993977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3078648447742160275991969 2308986335806620206993977)
              ·
                refine ⟨1731739751854965155245483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2308986335806620206993977 1731739751854965155245483)
                ·
                  refine ⟨2597609627782447732868225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1731739751854965155245483 2597609627782447732868225)
                  ·
                    refine ⟨1948207220836835799651169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2597609627782447732868225 1948207220836835799651169)
                    ·
                      refine ⟨1461155415627626849738377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1948207220836835799651169 1461155415627626849738377)
                      ·
                        rfl

theorem cell23_2845590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 3, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 3, 2, 2, 1, 2, 2].length) (baseStart_2845590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2845590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2845590 prefixEnd_2845590 := by exact prefixLift 2845590
  have htrace : WordTrace (prefixWord ++ tailWord_2845590) baseStart_2845590 baseEnd_2845590 := by
    simpa [prefixWord, tailWord_2845590, baseEnd_2845590] using wordTrace_append hprefix tailTrace_2845590
  have hstable : (prefixWord ++ tailWord_2845590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2845590).length < 2 ^ (prefixWord ++ tailWord_2845590).sum := by decide
  have hdescent : baseEnd_2845590 < baseStart_2845590 := by decide
  rcases family_descends (prefixWord ++ tailWord_2845590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2845591 : List Nat := [1, 1, 3, 3, 1, 2, 2, 2, 2, 2, 4]
def baseStart_2845591 : Nat := 118140960795 + 2845591 * 2 ^ 59
def prefixEnd_2845591 : Nat := 4983230072969 + 3 ^ 40 * 2845591 * 2
def baseEnd_2845591 : Nat := 1461155929108281345825871

theorem tailTrace_2845591 : CollatzResearch.WordTrace tailWord_2845591 prefixEnd_2845591 1461155929108281345825871 := by
  unfold tailWord_2845591
  simp only [CollatzResearch.WordTrace]
  refine ⟨103787230233917270096408627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69191486822611513397605751 103787230233917270096408627)
  ·
    refine ⟨155680845350875905144612941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103787230233917270096408627 155680845350875905144612941)
    ·
      refine ⟨58380317006578464429229853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 155680845350875905144612941 58380317006578464429229853)
      ·
        refine ⟨21892618877466924160961195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58380317006578464429229853 21892618877466924160961195)
        ·
          refine ⟨32838928316200386241441793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21892618877466924160961195 32838928316200386241441793)
          ·
            refine ⟨24629196237150289681081345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32838928316200386241441793 24629196237150289681081345)
            ·
              refine ⟨18471897177862717260811009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24629196237150289681081345 18471897177862717260811009)
              ·
                refine ⟨13853922883397037945608257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18471897177862717260811009 13853922883397037945608257)
                ·
                  refine ⟨10390442162547778459206193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13853922883397037945608257 10390442162547778459206193)
                  ·
                    refine ⟨7792831621910833844404645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10390442162547778459206193 7792831621910833844404645)
                    ·
                      refine ⟨1461155929108281345825871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7792831621910833844404645 1461155929108281345825871)
                      ·
                        rfl

theorem cell23_2845591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 2, 2, 2, 2, 4].length) (baseStart_2845591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2845591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2845591 prefixEnd_2845591 := by exact prefixLift 2845591
  have htrace : WordTrace (prefixWord ++ tailWord_2845591) baseStart_2845591 baseEnd_2845591 := by
    simpa [prefixWord, tailWord_2845591, baseEnd_2845591] using wordTrace_append hprefix tailTrace_2845591
  have hstable : (prefixWord ++ tailWord_2845591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2845591).length < 2 ^ (prefixWord ++ tailWord_2845591).sum := by decide
  have hdescent : baseEnd_2845591 < baseStart_2845591 := by decide
  rcases family_descends (prefixWord ++ tailWord_2845591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2845611 : List Nat := [1, 1, 1, 1, 2, 1, 1, 7, 2, 3, 3]
def baseStart_2845611 : Nat := 118140960795 + 2845611 * 2 ^ 59
def prefixEnd_2845611 : Nat := 4983230072969 + 3 ^ 40 * 2845611 * 2
def baseEnd_2845611 : Nat := 1461166198721371267575779

theorem tailTrace_2845611 : CollatzResearch.WordTrace tailWord_2845611 prefixEnd_2845611 1461166198721371267575779 := by
  unfold tailWord_2845611
  simp only [CollatzResearch.WordTrace]
  refine ⟨103787959693844813512136687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69191973129229875674757791 103787959693844813512136687)
  ·
    refine ⟨155681939540767220268205031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103787959693844813512136687 155681939540767220268205031)
    ·
      refine ⟨233522909311150830402307547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155681939540767220268205031 233522909311150830402307547)
      ·
        refine ⟨350284363966726245603461321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 233522909311150830402307547 350284363966726245603461321)
        ·
          refine ⟨262713272975044684202595991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 350284363966726245603461321 262713272975044684202595991)
          ·
            refine ⟨394069909462567026303893987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 262713272975044684202595991 394069909462567026303893987)
            ·
              refine ⟨591104864193850539455840981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 394069909462567026303893987 591104864193850539455840981)
              ·
                refine ⟨13854020254543372018496273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 591104864193850539455840981 13854020254543372018496273)
                ·
                  refine ⟨10390515190907529013872205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13854020254543372018496273 10390515190907529013872205)
                  ·
                    refine ⟨3896443196590323380202077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10390515190907529013872205 3896443196590323380202077)
                    ·
                      refine ⟨1461166198721371267575779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3896443196590323380202077 1461166198721371267575779)
                      ·
                        rfl

theorem cell23_2845611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 7, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 7, 2, 3, 3].length) (baseStart_2845611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2845611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2845611 prefixEnd_2845611 := by exact prefixLift 2845611
  have htrace : WordTrace (prefixWord ++ tailWord_2845611) baseStart_2845611 baseEnd_2845611 := by
    simpa [prefixWord, tailWord_2845611, baseEnd_2845611] using wordTrace_append hprefix tailTrace_2845611
  have hstable : (prefixWord ++ tailWord_2845611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2845611).length < 2 ^ (prefixWord ++ tailWord_2845611).sum := by decide
  have hdescent : baseEnd_2845611 < baseStart_2845611 := by decide
  rcases family_descends (prefixWord ++ tailWord_2845611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2845631 : List Nat := [1, 1, 2, 2, 2, 1, 2, 5, 2, 5]
def baseStart_2845631 : Nat := 118140960795 + 2845631 * 2 ^ 59
def prefixEnd_2845631 : Nat := 4983230072969 + 3 ^ 40 * 2845631 * 2
def baseEnd_2845631 : Nat := 487058822778153729775229

theorem tailTrace_2845631 : CollatzResearch.WordTrace tailWord_2845631 prefixEnd_2845631 487058822778153729775229 := by
  unfold tailWord_2845631
  simp only [CollatzResearch.WordTrace]
  refine ⟨103788689153772356927864747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69192459435848237951909831 103788689153772356927864747)
  ·
    refine ⟨155683033730658535391797121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103788689153772356927864747 155683033730658535391797121)
    ·
      refine ⟨116762275297993901543847841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 155683033730658535391797121 116762275297993901543847841)
      ·
        refine ⟨87571706473495426157885881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 116762275297993901543847841 87571706473495426157885881)
        ·
          refine ⟨65678779855121569618414411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87571706473495426157885881 65678779855121569618414411)
          ·
            refine ⟨98518169782682354427621617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65678779855121569618414411 98518169782682354427621617)
            ·
              refine ⟨73888627337011765820716213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 98518169782682354427621617 73888627337011765820716213)
              ·
                refine ⟨6927058812844853045692145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 73888627337011765820716213 6927058812844853045692145)
                ·
                  refine ⟨5195294109633639784269109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6927058812844853045692145 5195294109633639784269109)
                  ·
                    refine ⟨487058822778153729775229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5195294109633639784269109 487058822778153729775229)
                    ·
                      rfl

theorem cell23_2845631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 5, 2, 5].length) (baseStart_2845631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2845631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2845631 prefixEnd_2845631 := by exact prefixLift 2845631
  have htrace : WordTrace (prefixWord ++ tailWord_2845631) baseStart_2845631 baseEnd_2845631 := by
    simpa [prefixWord, tailWord_2845631, baseEnd_2845631] using wordTrace_append hprefix tailTrace_2845631
  have hstable : (prefixWord ++ tailWord_2845631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2845631).length < 2 ^ (prefixWord ++ tailWord_2845631).sum := by decide
  have hdescent : baseEnd_2845631 < baseStart_2845631 := by decide
  rcases family_descends (prefixWord ++ tailWord_2845631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2845668 : List Nat := [2, 3, 1, 1, 1, 1, 2, 3, 1, 6, 2]
def baseStart_2845668 : Nat := 118140960795 + 2845668 * 2 ^ 59
def prefixEnd_2845668 : Nat := 4983230072969 + 3 ^ 40 * 2845668 * 2
def baseEnd_2845668 : Nat := 1461195467118677544563017

theorem tailTrace_2845668 : CollatzResearch.WordTrace tailWord_2845668 prefixEnd_2845668 1461195467118677544563017 := by
  unfold tailWord_2845668
  simp only [CollatzResearch.WordTrace]
  refine ⟨51895019327319156123480829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69193359103092208164641105 51895019327319156123480829)
  ·
    refine ⟨19460632247744683546305311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51895019327319156123480829 19460632247744683546305311)
    ·
      refine ⟨29190948371617025319457967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19460632247744683546305311 29190948371617025319457967)
      ·
        refine ⟨43786422557425537979186951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29190948371617025319457967 43786422557425537979186951)
        ·
          refine ⟨65679633836138306968780427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43786422557425537979186951 65679633836138306968780427)
          ·
            refine ⟨98519450754207460453170641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65679633836138306968780427 98519450754207460453170641)
            ·
              refine ⟨73889588065655595339877981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 98519450754207460453170641 73889588065655595339877981)
              ·
                refine ⟨27708595524620848252454243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 73889588065655595339877981 27708595524620848252454243)
                ·
                  refine ⟨41562893286931272378681365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27708595524620848252454243 41562893286931272378681365)
                  ·
                    refine ⟨1948260622824903392750689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 41562893286931272378681365 1948260622824903392750689)
                    ·
                      refine ⟨1461195467118677544563017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1948260622824903392750689 1461195467118677544563017)
                      ·
                        rfl

theorem cell23_2845668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 3, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 3, 1, 6, 2].length) (baseStart_2845668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2845668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2845668 prefixEnd_2845668 := by exact prefixLift 2845668
  have htrace : WordTrace (prefixWord ++ tailWord_2845668) baseStart_2845668 baseEnd_2845668 := by
    simpa [prefixWord, tailWord_2845668, baseEnd_2845668] using wordTrace_append hprefix tailTrace_2845668
  have hstable : (prefixWord ++ tailWord_2845668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2845668).length < 2 ^ (prefixWord ++ tailWord_2845668).sum := by decide
  have hdescent : baseEnd_2845668 < baseStart_2845668 := by decide
  rcases family_descends (prefixWord ++ tailWord_2845668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2845688 : List Nat := [2, 1, 2, 1, 1, 3, 1, 5, 2, 2, 3]
def baseStart_2845688 : Nat := 118140960795 + 2845688 * 2 ^ 59
def prefixEnd_2845688 : Nat := 4983230072969 + 3 ^ 40 * 2845688 * 2
def baseEnd_2845688 : Nat := 1461205736731767466312925

theorem tailTrace_2845688 : CollatzResearch.WordTrace tailWord_2845688 prefixEnd_2845688 1461205736731767466312925 := by
  unfold tailWord_2845688
  simp only [CollatzResearch.WordTrace]
  refine ⟨51895384057282927831344859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69193845409710570441793145 51895384057282927831344859)
  ·
    refine ⟨77843076085924391747017289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51895384057282927831344859 77843076085924391747017289)
    ·
      refine ⟨58382307064443293810262967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77843076085924391747017289 58382307064443293810262967)
      ·
        refine ⟨87573460596664940715394451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58382307064443293810262967 87573460596664940715394451)
        ·
          refine ⟨131360190894997411073091677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87573460596664940715394451 131360190894997411073091677)
          ·
            refine ⟨49260071585624029152409379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 131360190894997411073091677 49260071585624029152409379)
            ·
              refine ⟨73890107378436043728614069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49260071585624029152409379 73890107378436043728614069)
              ·
                refine ⟨6927197566728379099557569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 73890107378436043728614069 6927197566728379099557569)
                ·
                  refine ⟨5195398175046284324668177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6927197566728379099557569 5195398175046284324668177)
                  ·
                    refine ⟨3896548631284713243501133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5195398175046284324668177 3896548631284713243501133)
                    ·
                      refine ⟨1461205736731767466312925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3896548631284713243501133 1461205736731767466312925)
                      ·
                        rfl

theorem cell23_2845688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 5, 2, 2, 3].length) (baseStart_2845688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2845688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2845688 prefixEnd_2845688 := by exact prefixLift 2845688
  have htrace : WordTrace (prefixWord ++ tailWord_2845688) baseStart_2845688 baseEnd_2845688 := by
    simpa [prefixWord, tailWord_2845688, baseEnd_2845688] using wordTrace_append hprefix tailTrace_2845688
  have hstable : (prefixWord ++ tailWord_2845688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2845688).length < 2 ^ (prefixWord ++ tailWord_2845688).sum := by decide
  have hdescent : baseEnd_2845688 < baseStart_2845688 := by decide
  rcases family_descends (prefixWord ++ tailWord_2845688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2845725 : List Nat := [1, 4, 2, 2, 3, 1, 1, 3, 6]
def baseStart_2845725 : Nat := 118140960795 + 2845725 * 2 ^ 59
def prefixEnd_2845725 : Nat := 4983230072969 + 3 ^ 40 * 2845725 * 2
def baseEnd_2845725 : Nat := 162358303946220424616695

theorem tailTrace_2845725 : CollatzResearch.WordTrace tailWord_2845725 prefixEnd_2845725 162358303946220424616695 := by
  unfold tailWord_2845725
  simp only [CollatzResearch.WordTrace]
  refine ⟨103792117615431810981786629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69194745076954540654524419 103792117615431810981786629)
  ·
    refine ⟨19461022052893464559084993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 103792117615431810981786629 19461022052893464559084993)
    ·
      refine ⟨14595766539670098419313745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19461022052893464559084993 14595766539670098419313745)
      ·
        refine ⟨10946824904752573814485309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14595766539670098419313745 10946824904752573814485309)
        ·
          refine ⟨4105059339282215180431991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10946824904752573814485309 4105059339282215180431991)
          ·
            refine ⟨6157589008923322770647987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4105059339282215180431991 6157589008923322770647987)
            ·
              refine ⟨9236383513384984155971981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6157589008923322770647987 9236383513384984155971981)
              ·
                refine ⟨3463643817519369058489493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9236383513384984155971981 3463643817519369058489493)
                ·
                  refine ⟨162358303946220424616695, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3463643817519369058489493 162358303946220424616695)
                  ·
                    rfl

theorem cell23_2845725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 1, 3, 6].length) (baseStart_2845725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2845725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2845725 prefixEnd_2845725 := by exact prefixLift 2845725
  have htrace : WordTrace (prefixWord ++ tailWord_2845725) baseStart_2845725 baseEnd_2845725 := by
    simpa [prefixWord, tailWord_2845725, baseEnd_2845725] using wordTrace_append hprefix tailTrace_2845725
  have hstable : (prefixWord ++ tailWord_2845725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2845725).length < 2 ^ (prefixWord ++ tailWord_2845725).sum := by decide
  have hdescent : baseEnd_2845725 < baseStart_2845725 := by decide
  rcases family_descends (prefixWord ++ tailWord_2845725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2845792 : List Nat := [2, 1, 1, 3, 2, 2, 3, 2, 3, 2, 2]
def baseStart_2845792 : Nat := 118140960795 + 2845792 * 2 ^ 59
def prefixEnd_2845792 : Nat := 4983230072969 + 3 ^ 40 * 2845792 * 2
def baseEnd_2845792 : Nat := 1461259138719835059412447

theorem tailTrace_2845792 : CollatzResearch.WordTrace tailWord_2845792 prefixEnd_2845792 1461259138719835059412447 := by
  unfold tailWord_2845792
  simp only [CollatzResearch.WordTrace]
  refine ⟨51897280653094540712237815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69196374204126054282983753 51897280653094540712237815)
  ·
    refine ⟨77845920979641811068356723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51897280653094540712237815 77845920979641811068356723)
    ·
      refine ⟨116768881469462716602535085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77845920979641811068356723 116768881469462716602535085)
      ·
        refine ⟨43788330551048518725950657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 116768881469462716602535085 43788330551048518725950657)
        ·
          refine ⟨32841247913286389044462993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43788330551048518725950657 32841247913286389044462993)
          ·
            refine ⟨24630935934964791783347245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32841247913286389044462993 24630935934964791783347245)
            ·
              refine ⟨9236600975611796918755217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24630935934964791783347245 9236600975611796918755217)
              ·
                refine ⟨6927450731708847689066413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9236600975611796918755217 6927450731708847689066413)
                ·
                  refine ⟨2597794024390817883399905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6927450731708847689066413 2597794024390817883399905)
                  ·
                    refine ⟨1948345518293113412549929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2597794024390817883399905 1948345518293113412549929)
                    ·
                      refine ⟨1461259138719835059412447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1948345518293113412549929 1461259138719835059412447)
                      ·
                        rfl

theorem cell23_2845792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 3, 2, 3, 2, 2].length) (baseStart_2845792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2845792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2845792 prefixEnd_2845792 := by exact prefixLift 2845792
  have htrace : WordTrace (prefixWord ++ tailWord_2845792) baseStart_2845792 baseEnd_2845792 := by
    simpa [prefixWord, tailWord_2845792, baseEnd_2845792] using wordTrace_append hprefix tailTrace_2845792
  have hstable : (prefixWord ++ tailWord_2845792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2845792).length < 2 ^ (prefixWord ++ tailWord_2845792).sum := by decide
  have hdescent : baseEnd_2845792 < baseStart_2845792 := by decide
  rcases family_descends (prefixWord ++ tailWord_2845792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2845795 : List Nat := [1, 1, 1, 5, 1, 1, 1, 6, 1, 2, 3]
def baseStart_2845795 : Nat := 118140960795 + 2845795 * 2 ^ 59
def prefixEnd_2845795 : Nat := 4983230072969 + 3 ^ 40 * 2845795 * 2
def baseEnd_2845795 : Nat := 1461260679161798547674933

theorem tailTrace_2845795 : CollatzResearch.WordTrace tailWord_2845795 prefixEnd_2845795 1461260679161798547674933 := by
  unfold tailWord_2845795
  simp only [CollatzResearch.WordTrace]
  refine ⟨103794670725178212936834839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69196447150118808624556559 103794670725178212936834839)
  ·
    refine ⟨155692006087767319405252259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103794670725178212936834839 155692006087767319405252259)
    ·
      refine ⟨233538009131650979107878389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155692006087767319405252259 233538009131650979107878389)
      ·
        refine ⟨21894188356092279291363599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 233538009131650979107878389 21894188356092279291363599)
        ·
          refine ⟨32841282534138418937045399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21894188356092279291363599 32841282534138418937045399)
          ·
            refine ⟨49261923801207628405568099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32841282534138418937045399 49261923801207628405568099)
            ·
              refine ⟨73892885701811442608352149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49261923801207628405568099 73892885701811442608352149)
              ·
                refine ⟨3463729017272411372266507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 73892885701811442608352149 3463729017272411372266507)
                ·
                  refine ⟨5195593525908617058399761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3463729017272411372266507 5195593525908617058399761)
                  ·
                    refine ⟨3896695144431462793799821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5195593525908617058399761 3896695144431462793799821)
                    ·
                      refine ⟨1461260679161798547674933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3896695144431462793799821 1461260679161798547674933)
                      ·
                        rfl

theorem cell23_2845795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 6, 1, 2, 3].length) (baseStart_2845795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2845795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2845795 prefixEnd_2845795 := by exact prefixLift 2845795
  have htrace : WordTrace (prefixWord ++ tailWord_2845795) baseStart_2845795 baseEnd_2845795 := by
    simpa [prefixWord, tailWord_2845795, baseEnd_2845795] using wordTrace_append hprefix tailTrace_2845795
  have hstable : (prefixWord ++ tailWord_2845795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2845795).length < 2 ^ (prefixWord ++ tailWord_2845795).sum := by decide
  have hdescent : baseEnd_2845795 < baseStart_2845795 := by decide
  rcases family_descends (prefixWord ++ tailWord_2845795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2845805 : List Nat := [1, 5, 1, 1, 2, 2, 2, 2, 1, 2, 4]
def baseStart_2845805 : Nat := 118140960795 + 2845805 * 2 ^ 59
def prefixEnd_2845805 : Nat := 4983230072969 + 3 ^ 40 * 2845805 * 2
def baseEnd_2845805 : Nat := 1461265813968343508549887

theorem tailTrace_2845805 : CollatzResearch.WordTrace tailWord_2845805 prefixEnd_2845805 1461265813968343508549887 := by
  unfold tailWord_2845805
  simp only [CollatzResearch.WordTrace]
  refine ⟨103795035455141984644698869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69196690303427989763132579 103795035455141984644698869)
  ·
    refine ⟨9730784573919561060440519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 103795035455141984644698869 9730784573919561060440519)
    ·
      refine ⟨14596176860879341590660779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9730784573919561060440519 14596176860879341590660779)
      ·
        refine ⟨21894265291319012385991169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14596176860879341590660779 21894265291319012385991169)
        ·
          refine ⟨16420698968489259289493377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21894265291319012385991169 16420698968489259289493377)
          ·
            refine ⟨12315524226366944467120033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16420698968489259289493377 12315524226366944467120033)
            ·
              refine ⟨9236643169775208350340025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12315524226366944467120033 9236643169775208350340025)
              ·
                refine ⟨6927482377331406262755019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9236643169775208350340025 6927482377331406262755019)
                ·
                  refine ⟨10391223565997109394132529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6927482377331406262755019 10391223565997109394132529)
                  ·
                    refine ⟨7793417674497832045599397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10391223565997109394132529 7793417674497832045599397)
                    ·
                      refine ⟨1461265813968343508549887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7793417674497832045599397 1461265813968343508549887)
                      ·
                        rfl

theorem cell23_2845805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 2, 2, 1, 2, 4].length) (baseStart_2845805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2845805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2845805 prefixEnd_2845805 := by exact prefixLift 2845805
  have htrace : WordTrace (prefixWord ++ tailWord_2845805) baseStart_2845805 baseEnd_2845805 := by
    simpa [prefixWord, tailWord_2845805, baseEnd_2845805] using wordTrace_append hprefix tailTrace_2845805
  have hstable : (prefixWord ++ tailWord_2845805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2845805).length < 2 ^ (prefixWord ++ tailWord_2845805).sum := by decide
  have hdescent : baseEnd_2845805 < baseStart_2845805 := by decide
  rcases family_descends (prefixWord ++ tailWord_2845805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2845835 : List Nat := [1, 1, 1, 1, 4, 1, 1, 3, 5, 3, 2]
def baseStart_2845835 : Nat := 118140960795 + 2845835 * 2 ^ 59
def prefixEnd_2845835 : Nat := 4983230072969 + 3 ^ 40 * 2845835 * 2
def baseEnd_2845835 : Nat := 1461281218387978391174749

theorem tailTrace_2845835 : CollatzResearch.WordTrace tailWord_2845835 prefixEnd_2845835 1461281218387978391174749 := by
  unfold tailWord_2845835
  simp only [CollatzResearch.WordTrace]
  refine ⟨103796129645033299768290959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69197419763355533178860639 103796129645033299768290959)
  ·
    refine ⟨155694194467549949652436439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103796129645033299768290959 155694194467549949652436439)
    ·
      refine ⟨233541291701324924478654659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155694194467549949652436439 233541291701324924478654659)
      ·
        refine ⟨350311937551987386717981989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 233541291701324924478654659 350311937551987386717981989)
        ·
          refine ⟨65683488290997635009621623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 350311937551987386717981989 65683488290997635009621623)
          ·
            refine ⟨98525232436496452514432435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65683488290997635009621623 98525232436496452514432435)
            ·
              refine ⟨147787848654744678771648653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 98525232436496452514432435 147787848654744678771648653)
              ·
                refine ⟨55420443245529254539368245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 147787848654744678771648653 55420443245529254539368245)
                ·
                  refine ⟨5195666554268367613065773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 55420443245529254539368245 5195666554268367613065773)
                  ·
                    refine ⟨1948374957850637854899665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5195666554268367613065773 1948374957850637854899665)
                    ·
                      refine ⟨1461281218387978391174749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1948374957850637854899665 1461281218387978391174749)
                      ·
                        rfl

theorem cell23_2845835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 3, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 3, 5, 3, 2].length) (baseStart_2845835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2845835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2845835 prefixEnd_2845835 := by exact prefixLift 2845835
  have htrace : WordTrace (prefixWord ++ tailWord_2845835) baseStart_2845835 baseEnd_2845835 := by
    simpa [prefixWord, tailWord_2845835, baseEnd_2845835] using wordTrace_append hprefix tailTrace_2845835
  have hstable : (prefixWord ++ tailWord_2845835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2845835).length < 2 ^ (prefixWord ++ tailWord_2845835).sum := by decide
  have hdescent : baseEnd_2845835 < baseStart_2845835 := by decide
  rcases family_descends (prefixWord ++ tailWord_2845835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2845842 : List Nat := [3, 2, 3, 1, 1, 2, 3, 1, 1, 3, 3]
def baseStart_2845842 : Nat := 118140960795 + 2845842 * 2 ^ 59
def prefixEnd_2845842 : Nat := 4983230072969 + 3 ^ 40 * 2845842 * 2
def baseEnd_2845842 : Nat := 1461284812752559863787217

theorem tailTrace_2845842 : CollatzResearch.WordTrace tailWord_2845842 prefixEnd_2845842 1461284812752559863787217 := by
  unfold tailWord_2845842
  simp only [CollatzResearch.WordTrace]
  refine ⟨25949096239001984990948945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69197589970671959975863853 25949096239001984990948945)
  ·
    refine ⟨19461822179251488743211709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25949096239001984990948945 19461822179251488743211709)
    ·
      refine ⟨7298183317219308278704391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19461822179251488743211709 7298183317219308278704391)
      ·
        refine ⟨10947274975828962418056587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7298183317219308278704391 10947274975828962418056587)
        ·
          refine ⟨16420912463743443627084881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10947274975828962418056587 16420912463743443627084881)
          ·
            refine ⟨12315684347807582720313661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16420912463743443627084881 12315684347807582720313661)
            ·
              refine ⟨4618381630427843520117623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12315684347807582720313661 4618381630427843520117623)
              ·
                refine ⟨6927572445641765280176435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4618381630427843520117623 6927572445641765280176435)
                ·
                  refine ⟨10391358668462647920264653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6927572445641765280176435 10391358668462647920264653)
                  ·
                    refine ⟨3896759500673492970099245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10391358668462647920264653 3896759500673492970099245)
                    ·
                      refine ⟨1461284812752559863787217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3896759500673492970099245 1461284812752559863787217)
                      ·
                        rfl

theorem cell23_2845842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 3, 1, 1, 3, 3].length) (baseStart_2845842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2845842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2845842 prefixEnd_2845842 := by exact prefixLift 2845842
  have htrace : WordTrace (prefixWord ++ tailWord_2845842) baseStart_2845842 baseEnd_2845842 := by
    simpa [prefixWord, tailWord_2845842, baseEnd_2845842] using wordTrace_append hprefix tailTrace_2845842
  have hstable : (prefixWord ++ tailWord_2845842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2845842).length < 2 ^ (prefixWord ++ tailWord_2845842).sum := by decide
  have hdescent : baseEnd_2845842 < baseStart_2845842 := by decide
  rcases family_descends (prefixWord ++ tailWord_2845842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2845939 : List Nat := [1, 1, 1, 2, 2, 7, 2, 2, 5]
def baseStart_2845939 : Nat := 118140960795 + 2845939 * 2 ^ 59
def prefixEnd_2845939 : Nat := 4983230072969 + 3 ^ 40 * 2845939 * 2
def baseEnd_2845939 : Nat := 162370513375116220474919

theorem tailTrace_2845939 : CollatzResearch.WordTrace tailWord_2845939 prefixEnd_2845939 162370513375116220474919 := by
  unfold tailWord_2845939
  simp only [CollatzResearch.WordTrace]
  refine ⟨103799922836656525530076871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69199948557771017020051247 103799922836656525530076871)
  ·
    refine ⟨155699884254984788295115307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103799922836656525530076871 155699884254984788295115307)
    ·
      refine ⟨233549826382477182442672961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155699884254984788295115307 233549826382477182442672961)
      ·
        refine ⟨175162369786857886832004721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 233549826382477182442672961 175162369786857886832004721)
        ·
          refine ⟨131371777340143415124003541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 175162369786857886832004721 131371777340143415124003541)
          ·
            refine ⟨3079026031409611291968833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 131371777340143415124003541 3079026031409611291968833)
            ·
              refine ⟨2309269523557208468976625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3079026031409611291968833 2309269523557208468976625)
              ·
                refine ⟨1731952142667906351732469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2309269523557208468976625 1731952142667906351732469)
                ·
                  refine ⟨162370513375116220474919, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1731952142667906351732469 162370513375116220474919)
                  ·
                    rfl

theorem cell23_2845939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 7, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 7, 2, 2, 5].length) (baseStart_2845939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2845939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2845939 prefixEnd_2845939 := by exact prefixLift 2845939
  have htrace : WordTrace (prefixWord ++ tailWord_2845939) baseStart_2845939 baseEnd_2845939 := by
    simpa [prefixWord, tailWord_2845939, baseEnd_2845939] using wordTrace_append hprefix tailTrace_2845939
  have hstable : (prefixWord ++ tailWord_2845939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2845939).length < 2 ^ (prefixWord ++ tailWord_2845939).sum := by decide
  have hdescent : baseEnd_2845939 < baseStart_2845939 := by decide
  rcases family_descends (prefixWord ++ tailWord_2845939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2846025 : List Nat := [1, 2, 1, 1, 2, 3, 2, 3, 3, 5]
def baseStart_2846025 : Nat := 118140960795 + 2846025 * 2 ^ 59
def prefixEnd_2846025 : Nat := 4983230072969 + 3 ^ 40 * 2846025 * 2
def baseEnd_2846025 : Nat := 487126259904110882599625

theorem tailTrace_2846025 : CollatzResearch.WordTrace tailWord_2846025 prefixEnd_2846025 487126259904110882599625 := by
  unfold tailWord_2846025
  simp only [CollatzResearch.WordTrace]
  refine ⟨103803059514344962217707529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69202039676229974811805019 103803059514344962217707529)
  ·
    refine ⟨77852294635758721663280647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103803059514344962217707529 77852294635758721663280647)
    ·
      refine ⟨116778441953638082494920971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77852294635758721663280647 116778441953638082494920971)
      ·
        refine ⟨175167662930457123742381457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116778441953638082494920971 175167662930457123742381457)
        ·
          refine ⟨131375747197842842806786093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 175167662930457123742381457 131375747197842842806786093)
          ·
            refine ⟨49265905199191066052544785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 131375747197842842806786093 49265905199191066052544785)
            ·
              refine ⟨36949428899393299539408589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49265905199191066052544785 36949428899393299539408589)
              ·
                refine ⟨13856035837272487327278221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36949428899393299539408589 13856035837272487327278221)
                ·
                  refine ⟨5196013438977182747729333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13856035837272487327278221 5196013438977182747729333)
                  ·
                    refine ⟨487126259904110882599625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5196013438977182747729333 487126259904110882599625)
                    ·
                      rfl

theorem cell23_2846025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 3, 3, 5].length) (baseStart_2846025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2846025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2846025 prefixEnd_2846025 := by exact prefixLift 2846025
  have htrace : WordTrace (prefixWord ++ tailWord_2846025) baseStart_2846025 baseEnd_2846025 := by
    simpa [prefixWord, tailWord_2846025, baseEnd_2846025] using wordTrace_append hprefix tailTrace_2846025
  have hstable : (prefixWord ++ tailWord_2846025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2846025).length < 2 ^ (prefixWord ++ tailWord_2846025).sum := by decide
  have hdescent : baseEnd_2846025 < baseStart_2846025 := by decide
  rcases family_descends (prefixWord ++ tailWord_2846025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2846032 : List Nat := [2, 1, 1, 1, 1, 5, 1, 3, 1, 5, 2]
def baseStart_2846032 : Nat := 118140960795 + 2846032 * 2 ^ 59
def prefixEnd_2846032 : Nat := 4983230072969 + 3 ^ 40 * 2846032 * 2
def baseEnd_2846032 : Nat := 1461382374076914120411343

theorem tailTrace_2846032 : CollatzResearch.WordTrace tailWord_2846032 prefixEnd_2846032 1461382374076914120411343 := by
  unfold tailWord_2846032
  simp only [CollatzResearch.WordTrace]
  refine ⟨51901657412659801206606175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69202209883546401608808233 51901657412659801206606175)
  ·
    refine ⟨77852486118989701809909263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51901657412659801206606175 77852486118989701809909263)
    ·
      refine ⟨116778729178484552714863895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77852486118989701809909263 116778729178484552714863895)
      ·
        refine ⟨175168093767726829072295843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116778729178484552714863895 175168093767726829072295843)
        ·
          refine ⟨262752140651590243608443765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 175168093767726829072295843 262752140651590243608443765)
          ·
            refine ⟨24633013186086585338291603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 262752140651590243608443765 24633013186086585338291603)
            ·
              refine ⟨36949519779129878007437405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24633013186086585338291603 36949519779129878007437405)
              ·
                refine ⟨13856069917173704252789027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36949519779129878007437405 13856069917173704252789027)
                ·
                  refine ⟨20784104875760556379183541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13856069917173704252789027 20784104875760556379183541)
                  ·
                    refine ⟨1948509832102552160548457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 20784104875760556379183541 1948509832102552160548457)
                    ·
                      refine ⟨1461382374076914120411343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1948509832102552160548457 1461382374076914120411343)
                      ·
                        rfl

theorem cell23_2846032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 3, 1, 5, 2].length) (baseStart_2846032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2846032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2846032 prefixEnd_2846032 := by exact prefixLift 2846032
  have htrace : WordTrace (prefixWord ++ tailWord_2846032) baseStart_2846032 baseEnd_2846032 := by
    simpa [prefixWord, tailWord_2846032, baseEnd_2846032] using wordTrace_append hprefix tailTrace_2846032
  have hstable : (prefixWord ++ tailWord_2846032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2846032).length < 2 ^ (prefixWord ++ tailWord_2846032).sum := by decide
  have hdescent : baseEnd_2846032 < baseStart_2846032 := by decide
  rcases family_descends (prefixWord ++ tailWord_2846032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2846042 : List Nat := [3, 1, 1, 2, 1, 2, 4, 3, 1, 5]
def baseStart_2846042 : Nat := 118140960795 + 2846042 * 2 ^ 59
def prefixEnd_2846042 : Nat := 4983230072969 + 3 ^ 40 * 2846042 * 2
def baseEnd_2846042 : Nat := 487129169627819693762099

theorem tailTrace_2846042 : CollatzResearch.WordTrace tailWord_2846042 prefixEnd_2846042 487129169627819693762099 := by
  unfold tailWord_2846042
  simp only [CollatzResearch.WordTrace]
  refine ⟨25950919888820843530269095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69202453036855582747384253 25950919888820843530269095)
  ·
    refine ⟨38926379833231265295403643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25950919888820843530269095 38926379833231265295403643)
    ·
      refine ⟨58389569749846897943105465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38926379833231265295403643 58389569749846897943105465)
      ·
        refine ⟨43792177312385173457329099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58389569749846897943105465 43792177312385173457329099)
        ·
          refine ⟨65688265968577760185993649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43792177312385173457329099 65688265968577760185993649)
          ·
            refine ⟨49266199476433320139495237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65688265968577760185993649 49266199476433320139495237)
            ·
              refine ⟨9237412401831247526155357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 49266199476433320139495237 9237412401831247526155357)
              ·
                refine ⟨3464029650686717822308259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9237412401831247526155357 3464029650686717822308259)
                ·
                  refine ⟨5196044476030076733462389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3464029650686717822308259 5196044476030076733462389)
                  ·
                    refine ⟨487129169627819693762099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5196044476030076733462389 487129169627819693762099)
                    ·
                      rfl

theorem cell23_2846042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 4, 3, 1, 5].length) (baseStart_2846042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2846042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2846042 prefixEnd_2846042 := by exact prefixLift 2846042
  have htrace : WordTrace (prefixWord ++ tailWord_2846042) baseStart_2846042 baseEnd_2846042 := by
    simpa [prefixWord, tailWord_2846042, baseEnd_2846042] using wordTrace_append hprefix tailTrace_2846042
  have hstable : (prefixWord ++ tailWord_2846042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2846042).length < 2 ^ (prefixWord ++ tailWord_2846042).sum := by decide
  have hdescent : baseEnd_2846042 < baseStart_2846042 := by decide
  rcases family_descends (prefixWord ++ tailWord_2846042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2846075 : List Nat := [1, 1, 1, 1, 1, 6, 1, 3, 1, 1, 6]
def baseStart_2846075 : Nat := 118140960795 + 2846075 * 2 ^ 59
def prefixEnd_2846075 : Nat := 4983230072969 + 3 ^ 40 * 2846075 * 2
def baseEnd_2846075 : Nat := 1461404453745057452173645

theorem tailTrace_2846075 : CollatzResearch.WordTrace tailWord_2846075 prefixEnd_2846075 1461404453745057452173645 := by
  unfold tailWord_2846075
  simp only [CollatzResearch.WordTrace]
  refine ⟨103804883164163820757027679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69203255442775880504685119 103804883164163820757027679)
  ·
    refine ⟨155707324746245731135541519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103804883164163820757027679 155707324746245731135541519)
    ·
      refine ⟨233560987119368596703312279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155707324746245731135541519 233560987119368596703312279)
      ·
        refine ⟨350341480679052895054968419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 233560987119368596703312279 350341480679052895054968419)
        ·
          refine ⟨525512221018579342582452629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 350341480679052895054968419 525512221018579342582452629)
          ·
            refine ⟨24633385360245906683552467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 525512221018579342582452629 24633385360245906683552467)
            ·
              refine ⟨36950078040368860025328701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24633385360245906683552467 36950078040368860025328701)
              ·
                refine ⟨13856279265138322509498263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36950078040368860025328701 13856279265138322509498263)
                ·
                  refine ⟨20784418897707483764247395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13856279265138322509498263 20784418897707483764247395)
                  ·
                    refine ⟨31176628346561225646371093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20784418897707483764247395 31176628346561225646371093)
                    ·
                      refine ⟨1461404453745057452173645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 31176628346561225646371093 1461404453745057452173645)
                      ·
                        rfl

theorem cell23_2846075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 3, 1, 1, 6].length) (baseStart_2846075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2846075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2846075 prefixEnd_2846075 := by exact prefixLift 2846075
  have htrace : WordTrace (prefixWord ++ tailWord_2846075) baseStart_2846075 baseEnd_2846075 := by
    simpa [prefixWord, tailWord_2846075, baseEnd_2846075] using wordTrace_append hprefix tailTrace_2846075
  have hstable : (prefixWord ++ tailWord_2846075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2846075).length < 2 ^ (prefixWord ++ tailWord_2846075).sum := by decide
  have hdescent : baseEnd_2846075 < baseStart_2846075 := by decide
  rcases family_descends (prefixWord ++ tailWord_2846075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2846085 : List Nat := [1, 3, 1, 1, 3, 1, 4, 9]
def baseStart_2846085 : Nat := 118140960795 + 2846085 * 2 ^ 59
def prefixEnd_2846085 : Nat := 4983230072969 + 3 ^ 40 * 2846085 * 2
def baseEnd_2846085 : Nat := 54126281057466756038837

theorem tailTrace_2846085 : CollatzResearch.WordTrace tailWord_2846085 prefixEnd_2846085 54126281057466756038837 := by
  unfold tailWord_2846085
  simp only [CollatzResearch.WordTrace]
  refine ⟨103805247894127592464891709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69203498596085061643261139 103805247894127592464891709)
  ·
    refine ⟨38926967960297847174334391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 103805247894127592464891709 38926967960297847174334391)
    ·
      refine ⟨58390451940446770761501587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38926967960297847174334391 58390451940446770761501587)
      ·
        refine ⟨87585677910670156142252381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58390451940446770761501587 87585677910670156142252381)
        ·
          refine ⟨32844629216501308553344643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 87585677910670156142252381 32844629216501308553344643)
          ·
            refine ⟨49266943824751962830016965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32844629216501308553344643 49266943824751962830016965)
            ·
              refine ⟨9237551967140993030628181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 49266943824751962830016965 9237551967140993030628181)
              ·
                refine ⟨54126281057466756038837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 9237551967140993030628181 54126281057466756038837)
                ·
                  rfl

theorem cell23_2846085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 4, 9].length) (baseStart_2846085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2846085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2846085 prefixEnd_2846085 := by exact prefixLift 2846085
  have htrace : WordTrace (prefixWord ++ tailWord_2846085) baseStart_2846085 baseEnd_2846085 := by
    simpa [prefixWord, tailWord_2846085, baseEnd_2846085] using wordTrace_append hprefix tailTrace_2846085
  have hstable : (prefixWord ++ tailWord_2846085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2846085).length < 2 ^ (prefixWord ++ tailWord_2846085).sum := by decide
  have hdescent : baseEnd_2846085 < baseStart_2846085 := by decide
  rcases family_descends (prefixWord ++ tailWord_2846085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2846092 : List Nat := [2, 2, 1, 2, 1, 3, 3, 2, 1, 2, 4]
def baseStart_2846092 : Nat := 118140960795 + 2846092 * 2 ^ 59
def prefixEnd_2846092 : Nat := 4983230072969 + 3 ^ 40 * 2846092 * 2
def baseEnd_2846092 : Nat := 1461413182916183885661067

theorem tailTrace_2846092 : CollatzResearch.WordTrace tailWord_2846092 prefixEnd_2846092 1461413182916183885661067 := by
  unfold tailWord_2846092
  simp only [CollatzResearch.WordTrace]
  refine ⟨51902751602551116330198265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69203668803401488440264353 51902751602551116330198265)
  ·
    refine ⟨38927063701913337247648699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51902751602551116330198265 38927063701913337247648699)
    ·
      refine ⟨58390595552870005871473049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38927063701913337247648699 58390595552870005871473049)
      ·
        refine ⟨43792946664652504403604787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58390595552870005871473049 43792946664652504403604787)
        ·
          refine ⟨65689419996978756605407181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43792946664652504403604787 65689419996978756605407181)
          ·
            refine ⟨24633532498867033727027693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 65689419996978756605407181 24633532498867033727027693)
            ·
              refine ⟨9237574687075137647635385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24633532498867033727027693 9237574687075137647635385)
              ·
                refine ⟨6928181015306353235726539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9237574687075137647635385 6928181015306353235726539)
                ·
                  refine ⟨10392271522959529853589809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6928181015306353235726539 10392271522959529853589809)
                  ·
                    refine ⟨7794203642219647390192357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10392271522959529853589809 7794203642219647390192357)
                    ·
                      refine ⟨1461413182916183885661067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7794203642219647390192357 1461413182916183885661067)
                      ·
                        rfl

theorem cell23_2846092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 3, 2, 1, 2, 4].length) (baseStart_2846092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2846092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2846092 prefixEnd_2846092 := by exact prefixLift 2846092
  have htrace : WordTrace (prefixWord ++ tailWord_2846092) baseStart_2846092 baseEnd_2846092 := by
    simpa [prefixWord, tailWord_2846092, baseEnd_2846092] using wordTrace_append hprefix tailTrace_2846092
  have hstable : (prefixWord ++ tailWord_2846092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2846092).length < 2 ^ (prefixWord ++ tailWord_2846092).sum := by decide
  have hdescent : baseEnd_2846092 < baseStart_2846092 := by decide
  rcases family_descends (prefixWord ++ tailWord_2846092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2846112 : List Nat := [2, 1, 1, 4, 1, 2, 1, 2, 3, 3, 3]
def baseStart_2846112 : Nat := 118140960795 + 2846112 * 2 ^ 59
def prefixEnd_2846112 : Nat := 4983230072969 + 3 ^ 40 * 2846112 * 2
def baseEnd_2846112 : Nat := 1461423452529273807410975

theorem tailTrace_2846112 : CollatzResearch.WordTrace tailWord_2846112 prefixEnd_2846112 1461423452529273807410975 := by
  unfold tailWord_2846112
  simp only [CollatzResearch.WordTrace]
  refine ⟨51903116332514888038062295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69204155110019850717416393 51903116332514888038062295)
  ·
    refine ⟨77854674498772332057093443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51903116332514888038062295 77854674498772332057093443)
    ·
      refine ⟨116782011748158498085640165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77854674498772332057093443 116782011748158498085640165)
      ·
        refine ⟨21896627202779718391057531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 116782011748158498085640165 21896627202779718391057531)
        ·
          refine ⟨32844940804169577586586297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21896627202779718391057531 32844940804169577586586297)
          ·
            refine ⟨24633705603127183189939723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32844940804169577586586297 24633705603127183189939723)
            ·
              refine ⟨36950558404690774784909585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24633705603127183189939723 36950558404690774784909585)
              ·
                refine ⟨27712918803518081088682189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36950558404690774784909585 27712918803518081088682189)
                ·
                  refine ⟨10392344551319280408255821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27712918803518081088682189 10392344551319280408255821)
                  ·
                    refine ⟨3897129206744730153095933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10392344551319280408255821 3897129206744730153095933)
                    ·
                      refine ⟨1461423452529273807410975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3897129206744730153095933 1461423452529273807410975)
                      ·
                        rfl

theorem cell23_2846112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 2, 3, 3, 3].length) (baseStart_2846112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2846112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2846112 prefixEnd_2846112 := by exact prefixLift 2846112
  have htrace : WordTrace (prefixWord ++ tailWord_2846112) baseStart_2846112 baseEnd_2846112 := by
    simpa [prefixWord, tailWord_2846112, baseEnd_2846112] using wordTrace_append hprefix tailTrace_2846112
  have hstable : (prefixWord ++ tailWord_2846112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2846112).length < 2 ^ (prefixWord ++ tailWord_2846112).sum := by decide
  have hdescent : baseEnd_2846112 < baseStart_2846112 := by decide
  rcases family_descends (prefixWord ++ tailWord_2846112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2846115 : List Nat := [1, 1, 1, 4, 1, 3, 1, 1, 1, 9]
def baseStart_2846115 : Nat := 118140960795 + 2846115 * 2 ^ 59
def prefixEnd_2846115 : Nat := 4983230072969 + 3 ^ 40 * 2846115 * 2
def baseEnd_2846115 : Nat := 487141664323745765224487

theorem tailTrace_2846115 : CollatzResearch.WordTrace tailWord_2846115 prefixEnd_2846115 487141664323745765224487 := by
  unfold tailWord_2846115
  simp only [CollatzResearch.WordTrace]
  refine ⟨103806342084018907588483799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69204228056012605058989199 103806342084018907588483799)
  ·
    refine ⟨155709513126028361382725699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103806342084018907588483799 155709513126028361382725699)
    ·
      refine ⟨233564269689042542074088549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155709513126028361382725699 233564269689042542074088549)
      ·
        refine ⟨43793300566695476638891603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 233564269689042542074088549 43793300566695476638891603)
        ·
          refine ⟨65689950850043214958337405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43793300566695476638891603 65689950850043214958337405)
          ·
            refine ⟨24633731568766205609376527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 65689950850043214958337405 24633731568766205609376527)
            ·
              refine ⟨36950597353149308414064791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24633731568766205609376527 36950597353149308414064791)
              ·
                refine ⟨55425896029723962621097187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36950597353149308414064791 55425896029723962621097187)
                ·
                  refine ⟨83138844044585943931645781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 55425896029723962621097187 83138844044585943931645781)
                  ·
                    refine ⟨487141664323745765224487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 83138844044585943931645781 487141664323745765224487)
                    ·
                      rfl

theorem cell23_2846115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 1, 1, 9].length) (baseStart_2846115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2846115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2846115 prefixEnd_2846115 := by exact prefixLift 2846115
  have htrace : WordTrace (prefixWord ++ tailWord_2846115) baseStart_2846115 baseEnd_2846115 := by
    simpa [prefixWord, tailWord_2846115, baseEnd_2846115] using wordTrace_append hprefix tailTrace_2846115
  have hstable : (prefixWord ++ tailWord_2846115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2846115).length < 2 ^ (prefixWord ++ tailWord_2846115).sum := by decide
  have hdescent : baseEnd_2846115 < baseStart_2846115 := by decide
  rcases family_descends (prefixWord ++ tailWord_2846115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2846129 : List Nat := [1, 2, 2, 4, 1, 1, 4, 1, 1, 3, 3]
def baseStart_2846129 : Nat := 118140960795 + 2846129 * 2 ^ 59
def prefixEnd_2846129 : Nat := 4983230072969 + 3 ^ 40 * 2846129 * 2
def baseEnd_2846129 : Nat := 1461432181700400240898397

theorem tailTrace_2846129 : CollatzResearch.WordTrace tailWord_2846129 prefixEnd_2846129 1461432181700400240898397 := by
  unfold tailWord_2846129
  simp only [CollatzResearch.WordTrace]
  refine ⟨103806852705968187979493441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69204568470645458652995627 103806852705968187979493441)
  ·
    refine ⟨77855139529476140984620081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103806852705968187979493441 77855139529476140984620081)
    ·
      refine ⟨58391354647107105738465061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77855139529476140984620081 58391354647107105738465061)
      ·
        refine ⟨10948378996332582325962199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 58391354647107105738465061 10948378996332582325962199)
        ·
          refine ⟨16422568494498873488943299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10948378996332582325962199 16422568494498873488943299)
          ·
            refine ⟨24633852741748310233414949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16422568494498873488943299 24633852741748310233414949)
            ·
              refine ⟨4618847389077808168765303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24633852741748310233414949 4618847389077808168765303)
              ·
                refine ⟨6928271083616712253147955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4618847389077808168765303 6928271083616712253147955)
                ·
                  refine ⟨10392406625425068379721933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6928271083616712253147955 10392406625425068379721933)
                  ·
                    refine ⟨3897152484534400642395725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10392406625425068379721933 3897152484534400642395725)
                    ·
                      refine ⟨1461432181700400240898397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3897152484534400642395725 1461432181700400240898397)
                      ·
                        rfl

theorem cell23_2846129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 4, 1, 1, 3, 3].length) (baseStart_2846129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2846129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2846129 prefixEnd_2846129 := by exact prefixLift 2846129
  have htrace : WordTrace (prefixWord ++ tailWord_2846129) baseStart_2846129 baseEnd_2846129 := by
    simpa [prefixWord, tailWord_2846129, baseEnd_2846129] using wordTrace_append hprefix tailTrace_2846129
  have hstable : (prefixWord ++ tailWord_2846129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2846129).length < 2 ^ (prefixWord ++ tailWord_2846129).sum := by decide
  have hdescent : baseEnd_2846129 < baseStart_2846129 := by decide
  rcases family_descends (prefixWord ++ tailWord_2846129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2846142 : List Nat := [4, 2, 1, 1, 1, 1, 1, 3, 2, 2, 5]
def baseStart_2846142 : Nat := 118140960795 + 2846142 * 2 ^ 59
def prefixEnd_2846142 : Nat := 4983230072969 + 3 ^ 40 * 2846142 * 2
def baseEnd_2846142 : Nat := 1461438856948908690035837

theorem tailTrace_2846142 : CollatzResearch.WordTrace tailWord_2846142 prefixEnd_2846142 1461438856948908690035837 := by
  unfold tailWord_2846142
  simp only [CollatzResearch.WordTrace]
  refine ⟨12975915856865136399964585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 69204884569947394133144453 12975915856865136399964585)
  ·
    refine ⟨9731936892648852299973439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12975915856865136399964585 9731936892648852299973439)
    ·
      refine ⟨14597905338973278449960159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9731936892648852299973439 14597905338973278449960159)
      ·
        refine ⟨21896858008459917674940239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14597905338973278449960159 21896858008459917674940239)
        ·
          refine ⟨32845287012689876512410359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21896858008459917674940239 32845287012689876512410359)
          ·
            refine ⟨49267930519034814768615539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32845287012689876512410359 49267930519034814768615539)
            ·
              refine ⟨73901895778552222152923309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49267930519034814768615539 73901895778552222152923309)
              ·
                refine ⟨27713210916957083307346241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 73901895778552222152923309 27713210916957083307346241)
                ·
                  refine ⟨20784908187717812480509681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27713210916957083307346241 20784908187717812480509681)
                  ·
                    refine ⟨15588681140788359360382261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20784908187717812480509681 15588681140788359360382261)
                    ·
                      refine ⟨1461438856948908690035837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15588681140788359360382261 1461438856948908690035837)
                      ·
                        rfl

theorem cell23_2846142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 3, 2, 2, 5].length) (baseStart_2846142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2846142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2846142 prefixEnd_2846142 := by exact prefixLift 2846142
  have htrace : WordTrace (prefixWord ++ tailWord_2846142) baseStart_2846142 baseEnd_2846142 := by
    simpa [prefixWord, tailWord_2846142, baseEnd_2846142] using wordTrace_append hprefix tailTrace_2846142
  have hstable : (prefixWord ++ tailWord_2846142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2846142).length < 2 ^ (prefixWord ++ tailWord_2846142).sum := by decide
  have hdescent : baseEnd_2846142 < baseStart_2846142 := by decide
  rcases family_descends (prefixWord ++ tailWord_2846142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2846192 : List Nat := [2, 1, 1, 1, 3, 4, 2, 2, 7]
def baseStart_2846192 : Nat := 118140960795 + 2846192 * 2 ^ 59
def prefixEnd_2846192 : Nat := 4983230072969 + 3 ^ 40 * 2846192 * 2
def baseEnd_2846192 : Nat := 162384947886848166045623

theorem tailTrace_2846192 : CollatzResearch.WordTrace tailWord_2846192 prefixEnd_2846192 162384947886848166045623 := by
  unfold tailWord_2846192
  simp only [CollatzResearch.WordTrace]
  refine ⟨51904575252369974869518415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69206100336493299826024553 51904575252369974869518415)
  ·
    refine ⟨77856862878554962304277623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51904575252369974869518415 77856862878554962304277623)
    ·
      refine ⟨116785294317832443456416435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77856862878554962304277623 116785294317832443456416435)
      ·
        refine ⟨175177941476748665184624653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116785294317832443456416435 175177941476748665184624653)
        ·
          refine ⟨65691728053780749444234245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 175177941476748665184624653 65691728053780749444234245)
          ·
            refine ⟨12317199010083890520793921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 65691728053780749444234245 12317199010083890520793921)
            ·
              refine ⟨9237899257562917890595441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12317199010083890520793921 9237899257562917890595441)
              ·
                refine ⟨6928424443172188417946581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9237899257562917890595441 6928424443172188417946581)
                ·
                  refine ⟨162384947886848166045623, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6928424443172188417946581 162384947886848166045623)
                  ·
                    rfl

theorem cell23_2846192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 2, 2, 7].length) (baseStart_2846192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2846192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2846192 prefixEnd_2846192 := by exact prefixLift 2846192
  have htrace : WordTrace (prefixWord ++ tailWord_2846192) baseStart_2846192 baseEnd_2846192 := by
    simpa [prefixWord, tailWord_2846192, baseEnd_2846192] using wordTrace_append hprefix tailTrace_2846192
  have hstable : (prefixWord ++ tailWord_2846192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2846192).length < 2 ^ (prefixWord ++ tailWord_2846192).sum := by decide
  have hdescent : baseEnd_2846192 < baseStart_2846192 := by decide
  rcases family_descends (prefixWord ++ tailWord_2846192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2846259 : List Nat := [1, 1, 1, 2, 4, 3, 1, 3, 2, 1, 4]
def baseStart_2846259 : Nat := 118140960795 + 2846259 * 2 ^ 59
def prefixEnd_2846259 : Nat := 4983230072969 + 3 ^ 40 * 2846259 * 2
def baseEnd_2846259 : Nat := 1461498934185484732272799

theorem tailTrace_2846259 : CollatzResearch.WordTrace tailWord_2846259 prefixEnd_2846259 1461498934185484732272799 := by
  unfold tailWord_2846259
  simp only [CollatzResearch.WordTrace]
  refine ⟨103811594195497220181725831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69207729463664813454483887 103811594195497220181725831)
  ·
    refine ⟨155717391293245830272588747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103811594195497220181725831 155717391293245830272588747)
    ·
      refine ⟨233576086939868745408883121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155717391293245830272588747 233576086939868745408883121)
      ·
        refine ⟨175182065204901559056662341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 233576086939868745408883121 175182065204901559056662341)
        ·
          refine ⟨32846637225919042323124189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 175182065204901559056662341 32846637225919042323124189)
          ·
            refine ⟨12317488959719640871171571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32846637225919042323124189 12317488959719640871171571)
            ·
              refine ⟨18476233439579461306757357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12317488959719640871171571 18476233439579461306757357)
              ·
                refine ⟨6928587539842297990034009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18476233439579461306757357 6928587539842297990034009)
                ·
                  refine ⟨5196440654881723492525507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6928587539842297990034009 5196440654881723492525507)
                  ·
                    refine ⟨7794660982322585238788261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5196440654881723492525507 7794660982322585238788261)
                    ·
                      refine ⟨1461498934185484732272799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7794660982322585238788261 1461498934185484732272799)
                      ·
                        rfl

theorem cell23_2846259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 1, 3, 2, 1, 4].length) (baseStart_2846259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2846259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2846259 prefixEnd_2846259 := by exact prefixLift 2846259
  have htrace : WordTrace (prefixWord ++ tailWord_2846259) baseStart_2846259 baseEnd_2846259 := by
    simpa [prefixWord, tailWord_2846259, baseEnd_2846259] using wordTrace_append hprefix tailTrace_2846259
  have hstable : (prefixWord ++ tailWord_2846259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2846259).length < 2 ^ (prefixWord ++ tailWord_2846259).sum := by decide
  have hdescent : baseEnd_2846259 < baseStart_2846259 := by decide
  rcases family_descends (prefixWord ++ tailWord_2846259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2846272 : List Nat := [2, 1, 1, 2, 2, 2, 1, 3, 2, 1, 6]
def baseStart_2846272 : Nat := 118140960795 + 2846272 * 2 ^ 59
def prefixEnd_2846272 : Nat := 4983230072969 + 3 ^ 40 * 2846272 * 2
def baseEnd_2846272 : Nat := 1461505609433993181410239

theorem tailTrace_2846272 : CollatzResearch.WordTrace tailWord_2846272 prefixEnd_2846272 1461505609433993181410239 := by
  unfold tailWord_2846272
  simp only [CollatzResearch.WordTrace]
  refine ⟨51906034172225061700974535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69208045562966748934632713 51906034172225061700974535)
  ·
    refine ⟨77859051258337592551461803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51906034172225061700974535 77859051258337592551461803)
    ·
      refine ⟨116788576887506388827192705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77859051258337592551461803 116788576887506388827192705)
      ·
        refine ⟨87591432665629791620394529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 116788576887506388827192705 87591432665629791620394529)
        ·
          refine ⟨65693574499222343715295897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87591432665629791620394529 65693574499222343715295897)
          ·
            refine ⟨49270180874416757786471923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65693574499222343715295897 49270180874416757786471923)
            ·
              refine ⟨73905271311625136679707885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49270180874416757786471923 73905271311625136679707885)
              ·
                refine ⟨27714476741859426254890457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 73905271311625136679707885 27714476741859426254890457)
                ·
                  refine ⟨20785857556394569691167843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27714476741859426254890457 20785857556394569691167843)
                  ·
                    refine ⟨31178786334591854536751765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20785857556394569691167843 31178786334591854536751765)
                    ·
                      refine ⟨1461505609433993181410239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 31178786334591854536751765 1461505609433993181410239)
                      ·
                        rfl

theorem cell23_2846272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 3, 2, 1, 6].length) (baseStart_2846272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2846272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2846272 prefixEnd_2846272 := by exact prefixLift 2846272
  have htrace : WordTrace (prefixWord ++ tailWord_2846272) baseStart_2846272 baseEnd_2846272 := by
    simpa [prefixWord, tailWord_2846272, baseEnd_2846272] using wordTrace_append hprefix tailTrace_2846272
  have hstable : (prefixWord ++ tailWord_2846272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2846272).length < 2 ^ (prefixWord ++ tailWord_2846272).sum := by decide
  have hdescent : baseEnd_2846272 < baseStart_2846272 := by decide
  rcases family_descends (prefixWord ++ tailWord_2846272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2846336 : List Nat := [2, 1, 1, 2, 1, 4, 2, 1, 4, 3, 2]
def baseStart_2846336 : Nat := 118140960795 + 2846336 * 2 ^ 59
def prefixEnd_2846336 : Nat := 4983230072969 + 3 ^ 40 * 2846336 * 2
def baseEnd_2846336 : Nat := 1461538472195880931009945

theorem tailTrace_2846336 : CollatzResearch.WordTrace tailWord_2846336 prefixEnd_2846336 1461538472195880931009945 := by
  unfold tailWord_2846336
  simp only [CollatzResearch.WordTrace]
  refine ⟨51907201308109131166139431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69209601744145508221519241 51907201308109131166139431)
  ·
    refine ⟨77860801962163696749209147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51907201308109131166139431 77860801962163696749209147)
    ·
      refine ⟨116791202943245545123813721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77860801962163696749209147 116791202943245545123813721)
      ·
        refine ⟨87593402207434158842860291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 116791202943245545123813721 87593402207434158842860291)
        ·
          refine ⟨131390103311151238264290437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87593402207434158842860291 131390103311151238264290437)
          ·
            refine ⟨24635644370840857174554457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 131390103311151238264290437 24635644370840857174554457)
            ·
              refine ⟨18476733278130642880915843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24635644370840857174554457 18476733278130642880915843)
              ·
                refine ⟨27715099917195964321373765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18476733278130642880915843 27715099917195964321373765)
                ·
                  refine ⟨5196581234474243310257581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27715099917195964321373765 5196581234474243310257581)
                  ·
                    refine ⟨1948717962927841241346593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5196581234474243310257581 1948717962927841241346593)
                    ·
                      refine ⟨1461538472195880931009945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1948717962927841241346593 1461538472195880931009945)
                      ·
                        rfl

theorem cell23_2846336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 2, 1, 4, 3, 2].length) (baseStart_2846336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2846336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2846336 prefixEnd_2846336 := by exact prefixLift 2846336
  have htrace : WordTrace (prefixWord ++ tailWord_2846336) baseStart_2846336 baseEnd_2846336 := by
    simpa [prefixWord, tailWord_2846336, baseEnd_2846336] using wordTrace_append hprefix tailTrace_2846336
  have hstable : (prefixWord ++ tailWord_2846336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2846336).length < 2 ^ (prefixWord ++ tailWord_2846336).sum := by decide
  have hdescent : baseEnd_2846336 < baseStart_2846336 := by decide
  rcases family_descends (prefixWord ++ tailWord_2846336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2846343 : List Nat := [1, 1, 4, 2, 1, 4, 2, 1, 3, 1, 3]
def baseStart_2846343 : Nat := 118140960795 + 2846343 * 2 ^ 59
def prefixEnd_2846343 : Nat := 4983230072969 + 3 ^ 40 * 2846343 * 2
def baseEnd_2846343 : Nat := 1461542066560462403622413

theorem tailTrace_2846343 : CollatzResearch.WordTrace tailWord_2846343 prefixEnd_2846343 1461542066560462403622413 := by
  unfold tailWord_2846343
  simp only [CollatzResearch.WordTrace]
  refine ⟨103814657927192902527783683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69209771951461935018522455 103814657927192902527783683)
  ·
    refine ⟨155721986890789353791675525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103814657927192902527783683 155721986890789353791675525)
    ·
      refine ⟨29197872542023003835939161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 155721986890789353791675525 29197872542023003835939161)
      ·
        refine ⟨21898404406517252876954371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29197872542023003835939161 21898404406517252876954371)
        ·
          refine ⟨32847606609775879315431557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21898404406517252876954371 32847606609775879315431557)
          ·
            refine ⟨6158926239332977371643417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32847606609775879315431557 6158926239332977371643417)
            ·
              refine ⟨4619194679499733028732563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6158926239332977371643417 4619194679499733028732563)
              ·
                refine ⟨6928792019249599543098845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4619194679499733028732563 6928792019249599543098845)
                ·
                  refine ⟨2598297007218599828662067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6928792019249599543098845 2598297007218599828662067)
                  ·
                    refine ⟨3897445510827899742993101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2598297007218599828662067 3897445510827899742993101)
                    ·
                      refine ⟨1461542066560462403622413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3897445510827899742993101 1461542066560462403622413)
                      ·
                        rfl

theorem cell23_2846343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 2, 1, 3, 1, 3].length) (baseStart_2846343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2846343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2846343 prefixEnd_2846343 := by exact prefixLift 2846343
  have htrace : WordTrace (prefixWord ++ tailWord_2846343) baseStart_2846343 baseEnd_2846343 := by
    simpa [prefixWord, tailWord_2846343, baseEnd_2846343] using wordTrace_append hprefix tailTrace_2846343
  have hstable : (prefixWord ++ tailWord_2846343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2846343).length < 2 ^ (prefixWord ++ tailWord_2846343).sum := by decide
  have hdescent : baseEnd_2846343 < baseStart_2846343 := by decide
  rcases family_descends (prefixWord ++ tailWord_2846343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2846413 : List Nat := [1, 6, 2, 1, 1, 1, 2, 1, 1, 1, 6]
def baseStart_2846413 : Nat := 118140960795 + 2846413 * 2 ^ 59
def prefixEnd_2846413 : Nat := 4983230072969 + 3 ^ 40 * 2846413 * 2
def baseEnd_2846413 : Nat := 1461578010206277129747091

theorem tailTrace_2846413 : CollatzResearch.WordTrace tailWord_2846413 prefixEnd_2846413 1461578010206277129747091 := by
  unfold tailWord_2846413
  simp only [CollatzResearch.WordTrace]
  refine ⟨103817211036939304482831893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69211474024626202988554595 103817211036939304482831893)
  ·
    refine ⟨4866431767356529897632745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 103817211036939304482831893 4866431767356529897632745)
    ·
      refine ⟨3649823825517397423224559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4866431767356529897632745 3649823825517397423224559)
      ·
        refine ⟨5474735738276096134836839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3649823825517397423224559 5474735738276096134836839)
        ·
          refine ⟨8212103607414144202255259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5474735738276096134836839 8212103607414144202255259)
          ·
            refine ⟨12318155411121216303382889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8212103607414144202255259 12318155411121216303382889)
            ·
              refine ⟨9238616558340912227537167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12318155411121216303382889 9238616558340912227537167)
              ·
                refine ⟨13857924837511368341305751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9238616558340912227537167 13857924837511368341305751)
                ·
                  refine ⟨20786887256267052511958627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13857924837511368341305751 20786887256267052511958627)
                  ·
                    refine ⟨31180330884400578767937941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20786887256267052511958627 31180330884400578767937941)
                    ·
                      refine ⟨1461578010206277129747091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 31180330884400578767937941 1461578010206277129747091)
                      ·
                        rfl

theorem cell23_2846413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 2, 1, 1, 1, 6].length) (baseStart_2846413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2846413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2846413 prefixEnd_2846413 := by exact prefixLift 2846413
  have htrace : WordTrace (prefixWord ++ tailWord_2846413) baseStart_2846413 baseEnd_2846413 := by
    simpa [prefixWord, tailWord_2846413, baseEnd_2846413] using wordTrace_append hprefix tailTrace_2846413
  have hstable : (prefixWord ++ tailWord_2846413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2846413).length < 2 ^ (prefixWord ++ tailWord_2846413).sum := by decide
  have hdescent : baseEnd_2846413 < baseStart_2846413 := by decide
  rcases family_descends (prefixWord ++ tailWord_2846413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2846416 : List Nat := [2, 1, 1, 1, 1, 2, 1, 4, 6, 1, 3]
def baseStart_2846416 : Nat := 118140960795 + 2846416 * 2 ^ 59
def prefixEnd_2846416 : Nat := 4983230072969 + 3 ^ 40 * 2846416 * 2
def baseEnd_2846416 : Nat := 1461579550648240618009577

theorem tailTrace_2846416 : CollatzResearch.WordTrace tailWord_2846416 prefixEnd_2846416 1461579550648240618009577 := by
  unfold tailWord_2846416
  simp only [CollatzResearch.WordTrace]
  refine ⟨51908660227964217997595551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69211546970618957330127401 51908660227964217997595551)
  ·
    refine ⟨77862990341946326996393327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51908660227964217997595551 77862990341946326996393327)
    ·
      refine ⟨116794485512919490494589991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77862990341946326996393327 116794485512919490494589991)
      ·
        refine ⟨175191728269379235741884987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116794485512919490494589991 175191728269379235741884987)
        ·
          refine ⟨262787592404068853612827481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 175191728269379235741884987 262787592404068853612827481)
          ·
            refine ⟨197090694303051640209620611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 262787592404068853612827481 197090694303051640209620611)
            ·
              refine ⟨295636041454577460314430917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 197090694303051640209620611 295636041454577460314430917)
              ·
                refine ⟨55431757772733273808955797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 295636041454577460314430917 55431757772733273808955797)
                ·
                  refine ⟨2598363645596872209794803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 55431757772733273808955797 2598363645596872209794803)
                  ·
                    refine ⟨3897545468395308314692205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2598363645596872209794803 3897545468395308314692205)
                    ·
                      refine ⟨1461579550648240618009577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3897545468395308314692205 1461579550648240618009577)
                      ·
                        rfl

theorem cell23_2846416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 4, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 4, 6, 1, 3].length) (baseStart_2846416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2846416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2846416 prefixEnd_2846416 := by exact prefixLift 2846416
  have htrace : WordTrace (prefixWord ++ tailWord_2846416) baseStart_2846416 baseEnd_2846416 := by
    simpa [prefixWord, tailWord_2846416, baseEnd_2846416] using wordTrace_append hprefix tailTrace_2846416
  have hstable : (prefixWord ++ tailWord_2846416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2846416).length < 2 ^ (prefixWord ++ tailWord_2846416).sum := by decide
  have hdescent : baseEnd_2846416 < baseStart_2846416 := by decide
  rcases family_descends (prefixWord ++ tailWord_2846416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2846420 : List Nat := [2, 4, 1, 3, 1, 1, 3, 2, 1, 2, 3]
def baseStart_2846420 : Nat := 118140960795 + 2846420 * 2 ^ 59
def prefixEnd_2846420 : Nat := 4983230072969 + 3 ^ 40 * 2846420 * 2
def baseEnd_2846420 : Nat := 1461581604570858602359559

theorem tailTrace_2846420 : CollatzResearch.WordTrace tailWord_2846420 prefixEnd_2846420 1461581604570858602359559 := by
  unfold tailWord_2846420
  simp only [CollatzResearch.WordTrace]
  refine ⟨51908733173956972339168357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69211644231942629785557809 51908733173956972339168357)
  ·
    refine ⟨9732887470116932313594067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 51908733173956972339168357 9732887470116932313594067)
    ·
      refine ⟨14599331205175398470391101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9732887470116932313594067 14599331205175398470391101)
      ·
        refine ⟨5474749201940774426396663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14599331205175398470391101 5474749201940774426396663)
        ·
          refine ⟨8212123802911161639594995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5474749201940774426396663 8212123802911161639594995)
          ·
            refine ⟨12318185704366742459392493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8212123802911161639594995 12318185704366742459392493)
            ·
              refine ⟨4619319639137528422272185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12318185704366742459392493 4619319639137528422272185)
              ·
                refine ⟨3464489729353146316704139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4619319639137528422272185 3464489729353146316704139)
                ·
                  refine ⟨5196734594029719475056209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3464489729353146316704139 5196734594029719475056209)
                  ·
                    refine ⟨3897550945522289606292157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5196734594029719475056209 3897550945522289606292157)
                    ·
                      refine ⟨1461581604570858602359559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3897550945522289606292157 1461581604570858602359559)
                      ·
                        rfl

theorem cell23_2846420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 3, 2, 1, 2, 3].length) (baseStart_2846420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2846420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2846420 prefixEnd_2846420 := by exact prefixLift 2846420
  have htrace : WordTrace (prefixWord ++ tailWord_2846420) baseStart_2846420 baseEnd_2846420 := by
    simpa [prefixWord, tailWord_2846420, baseEnd_2846420] using wordTrace_append hprefix tailTrace_2846420
  have hstable : (prefixWord ++ tailWord_2846420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2846420).length < 2 ^ (prefixWord ++ tailWord_2846420).sum := by decide
  have hdescent : baseEnd_2846420 < baseStart_2846420 := by decide
  rcases family_descends (prefixWord ++ tailWord_2846420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2846433 : List Nat := [1, 2, 3, 1, 5, 1, 1, 2, 1, 3, 3]
def baseStart_2846433 : Nat := 118140960795 + 2846433 * 2 ^ 59
def prefixEnd_2846433 : Nat := 4983230072969 + 3 ^ 40 * 2846433 * 2
def baseEnd_2846433 : Nat := 1461588279819367051496999

theorem tailTrace_2846433 : CollatzResearch.WordTrace tailWord_2846433 prefixEnd_2846433 1461588279819367051496999 := by
  unfold tailWord_2846433
  simp only [CollatzResearch.WordTrace]
  refine ⟨103817940496866847898559953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69211960331244565265706635 103817940496866847898559953)
  ·
    refine ⟨77863455372650135923919965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103817940496866847898559953 77863455372650135923919965)
    ·
      refine ⟨29198795764743800971469987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 77863455372650135923919965 29198795764743800971469987)
      ·
        refine ⟨43798193647115701457204981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29198795764743800971469987 43798193647115701457204981)
        ·
          refine ⟨4106080654417097011612967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 43798193647115701457204981 4106080654417097011612967)
          ·
            refine ⟨6159120981625645517419451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4106080654417097011612967 6159120981625645517419451)
            ·
              refine ⟨9238681472438468276129177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6159120981625645517419451 9238681472438468276129177)
              ·
                refine ⟨6929011104328851207096883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9238681472438468276129177 6929011104328851207096883)
                ·
                  refine ⟨10393516656493276810645325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6929011104328851207096883 10393516656493276810645325)
                  ·
                    refine ⟨3897568746184978803991997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10393516656493276810645325 3897568746184978803991997)
                    ·
                      refine ⟨1461588279819367051496999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3897568746184978803991997 1461588279819367051496999)
                      ·
                        rfl

theorem cell23_2846433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 1, 2, 1, 3, 3].length) (baseStart_2846433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2846433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2846433 prefixEnd_2846433 := by exact prefixLift 2846433
  have htrace : WordTrace (prefixWord ++ tailWord_2846433) baseStart_2846433 baseEnd_2846433 := by
    simpa [prefixWord, tailWord_2846433, baseEnd_2846433] using wordTrace_append hprefix tailTrace_2846433
  have hstable : (prefixWord ++ tailWord_2846433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2846433).length < 2 ^ (prefixWord ++ tailWord_2846433).sum := by decide
  have hdescent : baseEnd_2846433 < baseStart_2846433 := by decide
  rcases family_descends (prefixWord ++ tailWord_2846433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2846443 : List Nat := [1, 1, 1, 1, 2, 4, 2, 5, 1, 3, 2]
def baseStart_2846443 : Nat := 118140960795 + 2846443 * 2 ^ 59
def prefixEnd_2846443 : Nat := 4983230072969 + 3 ^ 40 * 2846443 * 2
def baseEnd_2846443 : Nat := 1461593414625912012371953

theorem tailTrace_2846443 : CollatzResearch.WordTrace tailWord_2846443 prefixEnd_2846443 1461593414625912012371953 := by
  unfold tailWord_2846443
  simp only [CollatzResearch.WordTrace]
  refine ⟨103818305226830619606423983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69212203484553746404282655 103818305226830619606423983)
  ·
    refine ⟨155727457840245929409635975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103818305226830619606423983 155727457840245929409635975)
    ·
      refine ⟨233591186760368894114453963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155727457840245929409635975 233591186760368894114453963)
      ·
        refine ⟨350386780140553341171680945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 233591186760368894114453963 350386780140553341171680945)
        ·
          refine ⟨262790085105415005878760709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 350386780140553341171680945 262790085105415005878760709)
          ·
            refine ⟨49273140957265313602267633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 262790085105415005878760709 49273140957265313602267633)
            ·
              refine ⟨36954855717948985201700725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49273140957265313602267633 36954855717948985201700725)
              ·
                refine ⟨3464517723557717362659443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 36954855717948985201700725 3464517723557717362659443)
                ·
                  refine ⟨5196776585336576043989165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3464517723557717362659443 5196776585336576043989165)
                  ·
                    refine ⟨1948791219501216016495937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5196776585336576043989165 1948791219501216016495937)
                    ·
                      refine ⟨1461593414625912012371953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1948791219501216016495937 1461593414625912012371953)
                      ·
                        rfl

theorem cell23_2846443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 5, 1, 3, 2].length) (baseStart_2846443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2846443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2846443 prefixEnd_2846443 := by exact prefixLift 2846443
  have htrace : WordTrace (prefixWord ++ tailWord_2846443) baseStart_2846443 baseEnd_2846443 := by
    simpa [prefixWord, tailWord_2846443, baseEnd_2846443] using wordTrace_append hprefix tailTrace_2846443
  have hstable : (prefixWord ++ tailWord_2846443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2846443).length < 2 ^ (prefixWord ++ tailWord_2846443).sum := by decide
  have hdescent : baseEnd_2846443 < baseStart_2846443 := by decide
  rcases family_descends (prefixWord ++ tailWord_2846443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2846450 : List Nat := [3, 2, 1, 3, 1, 1, 4, 2, 2, 1, 3]
def baseStart_2846450 : Nat := 118140960795 + 2846450 * 2 ^ 59
def prefixEnd_2846450 : Nat := 4983230072969 + 3 ^ 40 * 2846450 * 2
def baseEnd_2846450 : Nat := 1461597008990493484984421

theorem tailTrace_2846450 : CollatzResearch.WordTrace tailWord_2846450 prefixEnd_2846450 1461597008990493484984421 := by
  unfold tailWord_2846450
  simp only [CollatzResearch.WordTrace]
  refine ⟨25954640134451314950482201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69212373691870173201285869 25954640134451314950482201)
  ·
    refine ⟨19465980100838486212861651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25954640134451314950482201 19465980100838486212861651)
    ·
      refine ⟨29198970151257729319292477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19465980100838486212861651 29198970151257729319292477)
      ·
        refine ⟨10949613806721648494734679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29198970151257729319292477 10949613806721648494734679)
        ·
          refine ⟨16424420710082472742102019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10949613806721648494734679 16424420710082472742102019)
          ·
            refine ⟨24636631065123709113153029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16424420710082472742102019 24636631065123709113153029)
            ·
              refine ⟨4619368324710695458716193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24636631065123709113153029 4619368324710695458716193)
              ·
                refine ⟨3464526243533021594037145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4619368324710695458716193 3464526243533021594037145)
                ·
                  refine ⟨2598394682649766195527859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3464526243533021594037145 2598394682649766195527859)
                  ·
                    refine ⟨3897592023974649293291789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2598394682649766195527859 3897592023974649293291789)
                    ·
                      refine ⟨1461597008990493484984421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3897592023974649293291789 1461597008990493484984421)
                      ·
                        rfl

theorem cell23_2846450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 4, 2, 2, 1, 3].length) (baseStart_2846450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2846450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2846450 prefixEnd_2846450 := by exact prefixLift 2846450
  have htrace : WordTrace (prefixWord ++ tailWord_2846450) baseStart_2846450 baseEnd_2846450 := by
    simpa [prefixWord, tailWord_2846450, baseEnd_2846450] using wordTrace_append hprefix tailTrace_2846450
  have hstable : (prefixWord ++ tailWord_2846450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2846450).length < 2 ^ (prefixWord ++ tailWord_2846450).sum := by decide
  have hdescent : baseEnd_2846450 < baseStart_2846450 := by decide
  rcases family_descends (prefixWord ++ tailWord_2846450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2846459 : List Nat := [1, 1, 1, 1, 1, 3, 1, 4, 4, 1, 5]
def baseStart_2846459 : Nat := 118140960795 + 2846459 * 2 ^ 59
def prefixEnd_2846459 : Nat := 4983230072969 + 3 ^ 40 * 2846459 * 2
def baseEnd_2846459 : Nat := 1461601630316383949771879

theorem tailTrace_2846459 : CollatzResearch.WordTrace tailWord_2846459 prefixEnd_2846459 1461601630316383949771879 := by
  unfold tailWord_2846459
  simp only [CollatzResearch.WordTrace]
  refine ⟨103818888794772654339006431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69212592529848436226004287 103818888794772654339006431)
  ·
    refine ⟨155728333192158981508509647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103818888794772654339006431 155728333192158981508509647)
    ·
      refine ⟨233592499788238472262764471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155728333192158981508509647 233592499788238472262764471)
      ·
        refine ⟨350388749682357708394146707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 233592499788238472262764471 350388749682357708394146707)
        ·
          refine ⟨525583124523536562591220061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 350388749682357708394146707 525583124523536562591220061)
          ·
            refine ⟨197093671696326210971707523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 525583124523536562591220061 197093671696326210971707523)
            ·
              refine ⟨295640507544489316457561285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 197093671696326210971707523 295640507544489316457561285)
              ·
                refine ⟨55432595164591746835792741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 295640507544489316457561285 55432595164591746835792741)
                ·
                  refine ⟨10393611593360952531711139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 55432595164591746835792741 10393611593360952531711139)
                  ·
                    refine ⟨15590417390041428797566709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10393611593360952531711139 15590417390041428797566709)
                    ·
                      refine ⟨1461601630316383949771879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15590417390041428797566709 1461601630316383949771879)
                      ·
                        rfl

theorem cell23_2846459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 4, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 4, 4, 1, 5].length) (baseStart_2846459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2846459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2846459 prefixEnd_2846459 := by exact prefixLift 2846459
  have htrace : WordTrace (prefixWord ++ tailWord_2846459) baseStart_2846459 baseEnd_2846459 := by
    simpa [prefixWord, tailWord_2846459, baseEnd_2846459] using wordTrace_append hprefix tailTrace_2846459
  have hstable : (prefixWord ++ tailWord_2846459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2846459).length < 2 ^ (prefixWord ++ tailWord_2846459).sum := by decide
  have hdescent : baseEnd_2846459 < baseStart_2846459 := by decide
  rcases family_descends (prefixWord ++ tailWord_2846459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2846473 : List Nat := [1, 2, 1, 1, 3, 2, 1, 2, 6, 2, 2]
def baseStart_2846473 : Nat := 118140960795 + 2846473 * 2 ^ 59
def prefixEnd_2846473 : Nat := 4983230072969 + 3 ^ 40 * 2846473 * 2
def baseEnd_2846473 : Nat := 1461608819045546894996815

theorem tailTrace_2846473 : CollatzResearch.WordTrace tailWord_2846473 prefixEnd_2846473 1461608819045546894996815 := by
  unfold tailWord_2846473
  simp only [CollatzResearch.WordTrace]
  refine ⟨103819399416721934730016073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69212932944481289820010715 103819399416721934730016073)
  ·
    refine ⟨77864549562541451047512055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103819399416721934730016073 77864549562541451047512055)
    ·
      refine ⟨116796824343812176571268083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77864549562541451047512055 116796824343812176571268083)
      ·
        refine ⟨175195236515718264856902125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116796824343812176571268083 175195236515718264856902125)
        ·
          refine ⟨65698213693394349321338297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 175195236515718264856902125 65698213693394349321338297)
          ·
            refine ⟨49273660270045761991003723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65698213693394349321338297 49273660270045761991003723)
            ·
              refine ⟨73910490405068642986505585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49273660270045761991003723 73910490405068642986505585)
              ·
                refine ⟨55432867803801482239879189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 73910490405068642986505585 55432867803801482239879189)
                ·
                  refine ⟨2598415678303194479994337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 55432867803801482239879189 2598415678303194479994337)
                  ·
                    refine ⟨1948811758727395859995753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2598415678303194479994337 1948811758727395859995753)
                    ·
                      refine ⟨1461608819045546894996815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1948811758727395859995753 1461608819045546894996815)
                      ·
                        rfl

theorem cell23_2846473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 2, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 2, 6, 2, 2].length) (baseStart_2846473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2846473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2846473 prefixEnd_2846473 := by exact prefixLift 2846473
  have htrace : WordTrace (prefixWord ++ tailWord_2846473) baseStart_2846473 baseEnd_2846473 := by
    simpa [prefixWord, tailWord_2846473, baseEnd_2846473] using wordTrace_append hprefix tailTrace_2846473
  have hstable : (prefixWord ++ tailWord_2846473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2846473).length < 2 ^ (prefixWord ++ tailWord_2846473).sum := by decide
  have hdescent : baseEnd_2846473 < baseStart_2846473 := by decide
  rcases family_descends (prefixWord ++ tailWord_2846473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2846513 : List Nat := [1, 2, 2, 3, 2, 2, 2, 4, 5]
def baseStart_2846513 : Nat := 118140960795 + 2846513 * 2 ^ 59
def prefixEnd_2846513 : Nat := 4983230072969 + 3 ^ 40 * 2846513 * 2
def baseEnd_2846513 : Nat := 162403262030191859832959

theorem tailTrace_2846513 : CollatzResearch.WordTrace tailWord_2846513 prefixEnd_2846513 162403262030191859832959 := by
  unfold tailWord_2846513
  simp only [CollatzResearch.WordTrace]
  refine ⟨103820858336577021561472193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69213905557718014374314795 103820858336577021561472193)
  ·
    refine ⟨77865643752432766171104145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103820858336577021561472193 77865643752432766171104145)
    ·
      refine ⟨58399232814324574628328109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77865643752432766171104145 58399232814324574628328109)
      ·
        refine ⟨21899712305371715485623041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58399232814324574628328109 21899712305371715485623041)
        ·
          refine ⟨16424784229028786614217281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21899712305371715485623041 16424784229028786614217281)
          ·
            refine ⟨12318588171771589960662961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16424784229028786614217281 12318588171771589960662961)
            ·
              refine ⟨9238941128828692470497221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12318588171771589960662961 9238941128828692470497221)
              ·
                refine ⟨1732301461655379838218229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9238941128828692470497221 1732301461655379838218229)
                ·
                  refine ⟨162403262030191859832959, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1732301461655379838218229 162403262030191859832959)
                  ·
                    rfl

theorem cell23_2846513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 2, 4, 5].length) (baseStart_2846513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2846513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2846513 prefixEnd_2846513 := by exact prefixLift 2846513
  have htrace : WordTrace (prefixWord ++ tailWord_2846513) baseStart_2846513 baseEnd_2846513 := by
    simpa [prefixWord, tailWord_2846513, baseEnd_2846513] using wordTrace_append hprefix tailTrace_2846513
  have hstable : (prefixWord ++ tailWord_2846513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2846513).length < 2 ^ (prefixWord ++ tailWord_2846513).sum := by decide
  have hdescent : baseEnd_2846513 < baseStart_2846513 := by decide
  rcases family_descends (prefixWord ++ tailWord_2846513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2846570 : List Nat := [3, 1, 3, 4, 1, 1, 1, 1, 1, 2, 5]
def baseStart_2846570 : Nat := 118140960795 + 2846570 * 2 ^ 59
def prefixEnd_2846570 : Nat := 4983230072969 + 3 ^ 40 * 2846570 * 2
def baseEnd_2846570 : Nat := 1461658626669033015483869

theorem tailTrace_2846570 : CollatzResearch.WordTrace tailWord_2846570 prefixEnd_2846570 1461658626669033015483869 := by
  unfold tailWord_2846570
  simp only [CollatzResearch.WordTrace]
  refine ⟨25955734324342630074074291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69215291531580346864198109 25955734324342630074074291)
  ·
    refine ⟨38933601486513945111111437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25955734324342630074074291 38933601486513945111111437)
    ·
      refine ⟨14600100557442729416666789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38933601486513945111111437 14600100557442729416666789)
      ·
        refine ⟨2737518854520511765625023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14600100557442729416666789 2737518854520511765625023)
        ·
          refine ⟨4106278281780767648437535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2737518854520511765625023 4106278281780767648437535)
          ·
            refine ⟨6159417422671151472656303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4106278281780767648437535 6159417422671151472656303)
            ·
              refine ⟨9239126134006727208984455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6159417422671151472656303 9239126134006727208984455)
              ·
                refine ⟨13858689201010090813476683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9239126134006727208984455 13858689201010090813476683)
                ·
                  refine ⟨20788033801515136220215025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13858689201010090813476683 20788033801515136220215025)
                  ·
                    refine ⟨15591025351136352165161269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20788033801515136220215025 15591025351136352165161269)
                    ·
                      refine ⟨1461658626669033015483869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15591025351136352165161269 1461658626669033015483869)
                      ·
                        rfl

theorem cell23_2846570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 1, 1, 1, 2, 5].length) (baseStart_2846570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2846570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2846570 prefixEnd_2846570 := by exact prefixLift 2846570
  have htrace : WordTrace (prefixWord ++ tailWord_2846570) baseStart_2846570 baseEnd_2846570 := by
    simpa [prefixWord, tailWord_2846570, baseEnd_2846570] using wordTrace_append hprefix tailTrace_2846570
  have hstable : (prefixWord ++ tailWord_2846570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2846570).length < 2 ^ (prefixWord ++ tailWord_2846570).sum := by decide
  have hdescent : baseEnd_2846570 < baseStart_2846570 := by decide
  rcases family_descends (prefixWord ++ tailWord_2846570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2846620 : List Nat := [2, 2, 3, 3, 1, 2, 2, 2, 6]
def baseStart_2846620 : Nat := 118140960795 + 2846620 * 2 ^ 59
def prefixEnd_2846620 : Nat := 4983230072969 + 3 ^ 40 * 2846620 * 2
def baseEnd_2846620 : Nat := 162409366744639757762071

theorem tailTrace_2846620 : CollatzResearch.WordTrace tailWord_2846620 prefixEnd_2846620 162409366744639757762071 := by
  unfold tailWord_2846620
  simp only [CollatzResearch.WordTrace]
  refine ⟨51912380473594689417808657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69216507298126252557078209 51912380473594689417808657)
  ·
    refine ⟨38934285355196017063356493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51912380473594689417808657 38934285355196017063356493)
    ·
      refine ⟨14600357008198506398758685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38934285355196017063356493 14600357008198506398758685)
      ·
        refine ⟨5475133878074439899534507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14600357008198506398758685 5475133878074439899534507)
        ·
          refine ⟨8212700817111659849301761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5475133878074439899534507 8212700817111659849301761)
          ·
            refine ⟨6159525612833744886976321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8212700817111659849301761 6159525612833744886976321)
            ·
              refine ⟨4619644209625308665232241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6159525612833744886976321 4619644209625308665232241)
              ·
                refine ⟨3464733157218981498924181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4619644209625308665232241 3464733157218981498924181)
                ·
                  refine ⟨162409366744639757762071, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3464733157218981498924181 162409366744639757762071)
                  ·
                    rfl

theorem cell23_2846620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 2, 2, 6].length) (baseStart_2846620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2846620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2846620 prefixEnd_2846620 := by exact prefixLift 2846620
  have htrace : WordTrace (prefixWord ++ tailWord_2846620) baseStart_2846620 baseEnd_2846620 := by
    simpa [prefixWord, tailWord_2846620, baseEnd_2846620] using wordTrace_append hprefix tailTrace_2846620
  have hstable : (prefixWord ++ tailWord_2846620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2846620).length < 2 ^ (prefixWord ++ tailWord_2846620).sum := by decide
  have hdescent : baseEnd_2846620 < baseStart_2846620 := by decide
  rcases family_descends (prefixWord ++ tailWord_2846620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2846636 : List Nat := [2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 4]
def baseStart_2846636 : Nat := 118140960795 + 2846636 * 2 ^ 59
def prefixEnd_2846636 : Nat := 4983230072969 + 3 ^ 40 * 2846636 * 2
def baseEnd_2846636 : Nat := 1461692516392229757258565

theorem tailTrace_2846636 : CollatzResearch.WordTrace tailWord_2846636 prefixEnd_2846636 1461692516392229757258565 := by
  unfold tailWord_2846636
  simp only [CollatzResearch.WordTrace]
  refine ⟨51912672257565706784099881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69216896343420942378799841 51912672257565706784099881)
  ·
    refine ⟨38934504193174280088074911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51912672257565706784099881 38934504193174280088074911)
    ·
      refine ⟨58401756289761420132112367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38934504193174280088074911 58401756289761420132112367)
      ·
        refine ⟨87602634434642130198168551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58401756289761420132112367 87602634434642130198168551)
        ·
          refine ⟨131403951651963195297252827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87602634434642130198168551 131403951651963195297252827)
          ·
            refine ⟨197105927477944792945879241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 131403951651963195297252827 197105927477944792945879241)
            ·
              refine ⟨147829445608458594709409431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 197105927477944792945879241 147829445608458594709409431)
              ·
                refine ⟨221744168412687892064114147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 147829445608458594709409431 221744168412687892064114147)
                ·
                  refine ⟨332616252619031838096171221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 221744168412687892064114147 332616252619031838096171221)
                  ·
                    refine ⟨7795693420758558705379013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 332616252619031838096171221 7795693420758558705379013)
                    ·
                      refine ⟨1461692516392229757258565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7795693420758558705379013 1461692516392229757258565)
                      ·
                        rfl

theorem cell23_2846636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 4].length) (baseStart_2846636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2846636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2846636 prefixEnd_2846636 := by exact prefixLift 2846636
  have htrace : WordTrace (prefixWord ++ tailWord_2846636) baseStart_2846636 baseEnd_2846636 := by
    simpa [prefixWord, tailWord_2846636, baseEnd_2846636] using wordTrace_append hprefix tailTrace_2846636
  have hstable : (prefixWord ++ tailWord_2846636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2846636).length < 2 ^ (prefixWord ++ tailWord_2846636).sum := by decide
  have hdescent : baseEnd_2846636 < baseStart_2846636 := by decide
  rcases family_descends (prefixWord ++ tailWord_2846636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2846663 : List Nat := [1, 1, 4, 1, 1, 2, 1, 4, 4, 4]
def baseStart_2846663 : Nat := 118140960795 + 2846663 * 2 ^ 59
def prefixEnd_2846663 : Nat := 4983230072969 + 3 ^ 40 * 2846663 * 2
def baseEnd_2846663 : Nat := 487235460123300383873647

theorem tailTrace_2846663 : CollatzResearch.WordTrace tailWord_2846663 prefixEnd_2846663 487235460123300383873647 := by
  unfold tailWord_2846663
  simp only [CollatzResearch.WordTrace]
  refine ⟨103826329286033597179432643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69217552857355731452955095 103826329286033597179432643)
  ·
    refine ⟨155739493929050395769148965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103826329286033597179432643 155739493929050395769148965)
    ·
      refine ⟨29201155111696949206715431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 155739493929050395769148965 29201155111696949206715431)
      ·
        refine ⟨43801732667545423810073147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29201155111696949206715431 43801732667545423810073147)
        ·
          refine ⟨65702599001318135715109721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43801732667545423810073147 65702599001318135715109721)
          ·
            refine ⟨49276949250988601786332291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65702599001318135715109721 49276949250988601786332291)
            ·
              refine ⟨73915423876482902679498437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49276949250988601786332291 73915423876482902679498437)
              ·
                refine ⟨13859141976840544252405957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 73915423876482902679498437 13859141976840544252405957)
                ·
                  refine ⟨2598589120657602047326117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13859141976840544252405957 2598589120657602047326117)
                  ·
                    refine ⟨487235460123300383873647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2598589120657602047326117 487235460123300383873647)
                    ·
                      rfl

theorem cell23_2846663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 4, 4, 4].length) (baseStart_2846663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2846663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2846663 prefixEnd_2846663 := by exact prefixLift 2846663
  have htrace : WordTrace (prefixWord ++ tailWord_2846663) baseStart_2846663 baseEnd_2846663 := by
    simpa [prefixWord, tailWord_2846663, baseEnd_2846663] using wordTrace_append hprefix tailTrace_2846663
  have hstable : (prefixWord ++ tailWord_2846663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2846663).length < 2 ^ (prefixWord ++ tailWord_2846663).sum := by decide
  have hdescent : baseEnd_2846663 < baseStart_2846663 := by decide
  rcases family_descends (prefixWord ++ tailWord_2846663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2846664 : List Nat := [2, 1, 3, 1, 4, 2, 2, 3, 1, 1, 3]
def baseStart_2846664 : Nat := 118140960795 + 2846664 * 2 ^ 59
def prefixEnd_2846664 : Nat := 4983230072969 + 3 ^ 40 * 2846664 * 2
def baseEnd_2846664 : Nat := 1461706893850555647708437

theorem tailTrace_2846664 : CollatzResearch.WordTrace tailWord_2846664 prefixEnd_2846664 1461706893850555647708437 := by
  unfold tailWord_2846664
  simp only [CollatzResearch.WordTrace]
  refine ⟨51913182879514987175109523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69217577172686649566812697 51913182879514987175109523)
  ·
    refine ⟨77869774319272480762664285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51913182879514987175109523 77869774319272480762664285)
    ·
      refine ⟨29201165369727180285999107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 77869774319272480762664285 29201165369727180285999107)
      ·
        refine ⟨43801748054590770428998661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29201165369727180285999107 43801748054590770428998661)
        ·
          refine ⟨8212827760235769455437249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 43801748054590770428998661 8212827760235769455437249)
          ·
            refine ⟨6159620820176827091577937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8212827760235769455437249 6159620820176827091577937)
            ·
              refine ⟨4619715615132620318683453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6159620820176827091577937 4619715615132620318683453)
              ·
                refine ⟨1732393355674732619506295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4619715615132620318683453 1732393355674732619506295)
                ·
                  refine ⟨2598590033512098929259443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1732393355674732619506295 2598590033512098929259443)
                  ·
                    refine ⟨3897885050268148393889165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2598590033512098929259443 3897885050268148393889165)
                    ·
                      refine ⟨1461706893850555647708437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3897885050268148393889165 1461706893850555647708437)
                      ·
                        rfl

theorem cell23_2846664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 2, 3, 1, 1, 3].length) (baseStart_2846664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2846664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2846664 prefixEnd_2846664 := by exact prefixLift 2846664
  have htrace : WordTrace (prefixWord ++ tailWord_2846664) baseStart_2846664 baseEnd_2846664 := by
    simpa [prefixWord, tailWord_2846664, baseEnd_2846664] using wordTrace_append hprefix tailTrace_2846664
  have hstable : (prefixWord ++ tailWord_2846664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2846664).length < 2 ^ (prefixWord ++ tailWord_2846664).sum := by decide
  have hdescent : baseEnd_2846664 < baseStart_2846664 := by decide
  rcases family_descends (prefixWord ++ tailWord_2846664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2846670 : List Nat := [4, 1, 1, 1, 2, 2, 3, 3, 1, 1, 4]
def baseStart_2846670 : Nat := 118140960795 + 2846670 * 2 ^ 59
def prefixEnd_2846670 : Nat := 4983230072969 + 3 ^ 40 * 2846670 * 2
def baseEnd_2846670 : Nat := 1461709974734482624233409

theorem tailTrace_2846670 : CollatzResearch.WordTrace tailWord_2846670 prefixEnd_2846670 1461709974734482624233409 := by
  unfold tailWord_2846670
  simp only [CollatzResearch.WordTrace]
  refine ⟨12978323074626029671867183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 69217723064672158249958309 12978323074626029671867183)
  ·
    refine ⟨19467484611939044507800775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12978323074626029671867183 19467484611939044507800775)
    ·
      refine ⟨29201226917908566761701163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19467484611939044507800775 29201226917908566761701163)
      ·
        refine ⟨43801840376862850142551745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29201226917908566761701163 43801840376862850142551745)
        ·
          refine ⟨32851380282647137606913809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43801840376862850142551745 32851380282647137606913809)
          ·
            refine ⟨24638535211985353205185357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32851380282647137606913809 24638535211985353205185357)
            ·
              refine ⟨9239450704494507451944509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24638535211985353205185357 9239450704494507451944509)
              ·
                refine ⟨3464794014185440294479191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9239450704494507451944509 3464794014185440294479191)
                ·
                  refine ⟨5197191021278160441718787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3464794014185440294479191 5197191021278160441718787)
                  ·
                    refine ⟨7795786531917240662578181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5197191021278160441718787 7795786531917240662578181)
                    ·
                      refine ⟨1461709974734482624233409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7795786531917240662578181 1461709974734482624233409)
                      ·
                        rfl

theorem cell23_2846670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 3, 3, 1, 1, 4].length) (baseStart_2846670 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2846670 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2846670 prefixEnd_2846670 := by exact prefixLift 2846670
  have htrace : WordTrace (prefixWord ++ tailWord_2846670) baseStart_2846670 baseEnd_2846670 := by
    simpa [prefixWord, tailWord_2846670, baseEnd_2846670] using wordTrace_append hprefix tailTrace_2846670
  have hstable : (prefixWord ++ tailWord_2846670).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2846670).length < 2 ^ (prefixWord ++ tailWord_2846670).sum := by decide
  have hdescent : baseEnd_2846670 < baseStart_2846670 := by decide
  rcases family_descends (prefixWord ++ tailWord_2846670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2846673 : List Nat := [1, 2, 2, 1, 2, 1, 2, 2, 5, 2, 3]
def baseStart_2846673 : Nat := 118140960795 + 2846673 * 2 ^ 59
def prefixEnd_2846673 : Nat := 4983230072969 + 3 ^ 40 * 2846673 * 2
def baseEnd_2846673 : Nat := 1461711515176446112495895

theorem tailTrace_2846673 : CollatzResearch.WordTrace tailWord_2846673 prefixEnd_2846673 1461711515176446112495895 := by
  unfold tailWord_2846673
  simp only [CollatzResearch.WordTrace]
  refine ⟨103826694015997368887296673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69217796010664912591531115 103826694015997368887296673)
  ·
    refine ⟨77870020511998026665472505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103826694015997368887296673 77870020511998026665472505)
    ·
      refine ⟨58402515383998519999104379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77870020511998026665472505 58402515383998519999104379)
      ·
        refine ⟨87603773075997779998656569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58402515383998519999104379 87603773075997779998656569)
        ·
          refine ⟨65702829806998334998992427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87603773075997779998656569 65702829806998334998992427)
          ·
            refine ⟨98554244710497502498488641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65702829806998334998992427 98554244710497502498488641)
            ·
              refine ⟨73915683532873126873866481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 98554244710497502498488641 73915683532873126873866481)
              ·
                refine ⟨55436762649654845155399861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 73915683532873126873866481 55436762649654845155399861)
                ·
                  refine ⟨5197196498405141733318737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 55436762649654845155399861 5197196498405141733318737)
                  ·
                    refine ⟨3897897373803856299989053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5197196498405141733318737 3897897373803856299989053)
                    ·
                      refine ⟨1461711515176446112495895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3897897373803856299989053 1461711515176446112495895)
                      ·
                        rfl

theorem cell23_2846673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 2, 5, 2, 3].length) (baseStart_2846673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2846673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2846673 prefixEnd_2846673 := by exact prefixLift 2846673
  have htrace : WordTrace (prefixWord ++ tailWord_2846673) baseStart_2846673 baseEnd_2846673 := by
    simpa [prefixWord, tailWord_2846673, baseEnd_2846673] using wordTrace_append hprefix tailTrace_2846673
  have hstable : (prefixWord ++ tailWord_2846673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2846673).length < 2 ^ (prefixWord ++ tailWord_2846673).sum := by decide
  have hdescent : baseEnd_2846673 < baseStart_2846673 := by decide
  rcases family_descends (prefixWord ++ tailWord_2846673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2846687 : List Nat := [1, 1, 2, 3, 4, 1, 1, 3, 3, 2, 2]
def baseStart_2846687 : Nat := 118140960795 + 2846687 * 2 ^ 59
def prefixEnd_2846687 : Nat := 4983230072969 + 3 ^ 40 * 2846687 * 2
def baseEnd_2846687 : Nat := 1461718703905609057720831

theorem tailTrace_2846687 : CollatzResearch.WordTrace tailWord_2846687 prefixEnd_2846687 1461718703905609057720831 := by
  unfold tailWord_2846687
  simp only [CollatzResearch.WordTrace]
  refine ⟨103827204637946649278306315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69218136425297766185537543 103827204637946649278306315)
  ·
    refine ⟨155740806956919973917459473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103827204637946649278306315 155740806956919973917459473)
    ·
      refine ⟨116805605217689980438094605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 155740806956919973917459473 116805605217689980438094605)
      ·
        refine ⟨43802101956633742664285477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 116805605217689980438094605 43802101956633742664285477)
        ·
          refine ⟨8212894116868826749553527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 43802101956633742664285477 8212894116868826749553527)
          ·
            refine ⟨12319341175303240124330291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8212894116868826749553527 12319341175303240124330291)
            ·
              refine ⟨18479011762954860186495437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12319341175303240124330291 18479011762954860186495437)
              ·
                refine ⟨6929629411108072569935789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18479011762954860186495437 6929629411108072569935789)
                ·
                  refine ⟨2598611029165527213725921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6929629411108072569935789 2598611029165527213725921)
                  ·
                    refine ⟨1948958271874145410294441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2598611029165527213725921 1948958271874145410294441)
                    ·
                      refine ⟨1461718703905609057720831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1948958271874145410294441 1461718703905609057720831)
                      ·
                        rfl

theorem cell23_2846687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 1, 3, 3, 2, 2].length) (baseStart_2846687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2846687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2846687 prefixEnd_2846687 := by exact prefixLift 2846687
  have htrace : WordTrace (prefixWord ++ tailWord_2846687) baseStart_2846687 baseEnd_2846687 := by
    simpa [prefixWord, tailWord_2846687, baseEnd_2846687] using wordTrace_append hprefix tailTrace_2846687
  have hstable : (prefixWord ++ tailWord_2846687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2846687).length < 2 ^ (prefixWord ++ tailWord_2846687).sum := by decide
  have hdescent : baseEnd_2846687 < baseStart_2846687 := by decide
  rcases family_descends (prefixWord ++ tailWord_2846687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2846710 : List Nat := [5, 1, 1, 1, 4, 1, 1, 9]
def baseStart_2846710 : Nat := 118140960795 + 2846710 * 2 ^ 59
def prefixEnd_2846710 : Nat := 4983230072969 + 3 ^ 40 * 2846710 * 2
def baseEnd_2846710 : Nat := 54138167183728239545675

theorem tailTrace_2846710 : CollatzResearch.WordTrace tailWord_2846710 prefixEnd_2846710 54138167183728239545675 := by
  unfold tailWord_2846710
  simp only [CollatzResearch.WordTrace]
  refine ⟨6489252719803957762899599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 69218695677908882804262389 6489252719803957762899599)
  ·
    refine ⟨9733879079705936644349399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6489252719803957762899599 9733879079705936644349399)
    ·
      refine ⟨14600818619558904966524099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9733879079705936644349399 14600818619558904966524099)
      ·
        refine ⟨21901227929338357449786149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14600818619558904966524099 21901227929338357449786149)
        ·
          refine ⟨4106480236750942021834903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21901227929338357449786149 4106480236750942021834903)
          ·
            refine ⟨6159720355126413032752355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4106480236750942021834903 6159720355126413032752355)
            ·
              refine ⟨9239580532689619549128533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6159720355126413032752355 9239580532689619549128533)
              ·
                refine ⟨54138167183728239545675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 9239580532689619549128533 54138167183728239545675)
                ·
                  rfl

theorem cell23_2846710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 1, 9].length) (baseStart_2846710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2846710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2846710 prefixEnd_2846710 := by exact prefixLift 2846710
  have htrace : WordTrace (prefixWord ++ tailWord_2846710) baseStart_2846710 baseEnd_2846710 := by
    simpa [prefixWord, tailWord_2846710, baseEnd_2846710] using wordTrace_append hprefix tailTrace_2846710
  have hstable : (prefixWord ++ tailWord_2846710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2846710).length < 2 ^ (prefixWord ++ tailWord_2846710).sum := by decide
  have hdescent : baseEnd_2846710 < baseStart_2846710 := by decide
  rcases family_descends (prefixWord ++ tailWord_2846710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2846763 : List Nat := [1, 1, 1, 1, 2, 1, 4, 1, 4, 4, 3]
def baseStart_2846763 : Nat := 118140960795 + 2846763 * 2 ^ 59
def prefixEnd_2846763 : Nat := 4983230072969 + 3 ^ 40 * 2846763 * 2
def baseEnd_2846763 : Nat := 1461757728435350760370481

theorem tailTrace_2846763 : CollatzResearch.WordTrace tailWord_2846763 prefixEnd_2846763 1461757728435350760370481 := by
  unfold tailWord_2846763
  simp only [CollatzResearch.WordTrace]
  refine ⟨103829976585671314258072943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69219984390447542838715295 103829976585671314258072943)
  ·
    refine ⟨155744964878506971387109415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103829976585671314258072943 155744964878506971387109415)
    ·
      refine ⟨233617447317760457080664123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155744964878506971387109415 233617447317760457080664123)
      ·
        refine ⟨350426170976640685620996185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 233617447317760457080664123 350426170976640685620996185)
        ·
          refine ⟨262819628232480514215747139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 350426170976640685620996185 262819628232480514215747139)
          ·
            refine ⟨394229442348720771323620709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 262819628232480514215747139 394229442348720771323620709)
            ·
              refine ⟨73918020440385144623178883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 394229442348720771323620709 73918020440385144623178883)
              ·
                refine ⟨110877030660577716934768325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 73918020440385144623178883 110877030660577716934768325)
                ·
                  refine ⟨20789443248858321925269061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 110877030660577716934768325 20789443248858321925269061)
                  ·
                    refine ⟨3898020609160935360987949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20789443248858321925269061 3898020609160935360987949)
                    ·
                      refine ⟨1461757728435350760370481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3898020609160935360987949 1461757728435350760370481)
                      ·
                        rfl

theorem cell23_2846763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 1, 4, 4, 3].length) (baseStart_2846763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2846763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2846763 prefixEnd_2846763 := by exact prefixLift 2846763
  have htrace : WordTrace (prefixWord ++ tailWord_2846763) baseStart_2846763 baseEnd_2846763 := by
    simpa [prefixWord, tailWord_2846763, baseEnd_2846763] using wordTrace_append hprefix tailTrace_2846763
  have hstable : (prefixWord ++ tailWord_2846763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2846763).length < 2 ^ (prefixWord ++ tailWord_2846763).sum := by decide
  have hdescent : baseEnd_2846763 < baseStart_2846763 := by decide
  rcases family_descends (prefixWord ++ tailWord_2846763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2846810 : List Nat := [3, 1, 1, 2, 1, 1, 5, 1, 2, 3, 3]
def baseStart_2846810 : Nat := 118140960795 + 2846810 * 2 ^ 59
def prefixEnd_2846810 : Nat := 4983230072969 + 3 ^ 40 * 2846810 * 2
def baseEnd_2846810 : Nat := 1461781862026112076482765

theorem tailTrace_2846810 : CollatzResearch.WordTrace tailWord_2846810 prefixEnd_2846810 1461781862026112076482765 := by
  unfold tailWord_2846810
  simp only [CollatzResearch.WordTrace]
  refine ⟨25957922704125260321258471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69221127211000694190022589 25957922704125260321258471)
  ·
    refine ⟨38936884056187890481887707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25957922704125260321258471 38936884056187890481887707)
    ·
      refine ⟨58405326084281835722831561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38936884056187890481887707 58405326084281835722831561)
      ·
        refine ⟨43803994563211376792123671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58405326084281835722831561 43803994563211376792123671)
        ·
          refine ⟨65705991844817065188185507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43803994563211376792123671 65705991844817065188185507)
          ·
            refine ⟨98558987767225597782278261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65705991844817065188185507 98558987767225597782278261)
            ·
              refine ⟨9239905103177399792088587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 98558987767225597782278261 9239905103177399792088587)
              ·
                refine ⟨13859857654766099688132881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9239905103177399792088587 13859857654766099688132881)
                ·
                  refine ⟨10394893241074574766099661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13859857654766099688132881 10394893241074574766099661)
                  ·
                    refine ⟨3898084965402965537287373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10394893241074574766099661 3898084965402965537287373)
                    ·
                      refine ⟨1461781862026112076482765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3898084965402965537287373 1461781862026112076482765)
                      ·
                        rfl

theorem cell23_2846810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 5, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 5, 1, 2, 3, 3].length) (baseStart_2846810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2846810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2846810 prefixEnd_2846810 := by exact prefixLift 2846810
  have htrace : WordTrace (prefixWord ++ tailWord_2846810) baseStart_2846810 baseEnd_2846810 := by
    simpa [prefixWord, tailWord_2846810, baseEnd_2846810] using wordTrace_append hprefix tailTrace_2846810
  have hstable : (prefixWord ++ tailWord_2846810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2846810).length < 2 ^ (prefixWord ++ tailWord_2846810).sum := by decide
  have hdescent : baseEnd_2846810 < baseStart_2846810 := by decide
  rcases family_descends (prefixWord ++ tailWord_2846810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2846830 : List Nat := [4, 1, 2, 2, 1, 1, 3, 1, 1, 7]
def baseStart_2846830 : Nat := 118140960795 + 2846830 * 2 ^ 59
def prefixEnd_2846830 : Nat := 4983230072969 + 3 ^ 40 * 2846830 * 2
def baseEnd_2846830 : Nat := 487264043879733999410891

theorem tailTrace_2846830 : CollatzResearch.WordTrace tailWord_2846830 prefixEnd_2846830 487264043879733999410891 := by
  unfold tailWord_2846830
  simp only [CollatzResearch.WordTrace]
  refine ⟨12979052534553573087595243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 69221613517619056467174629 12979052534553573087595243)
  ·
    refine ⟨19468578801830359631392865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12979052534553573087595243 19468578801830359631392865)
    ·
      refine ⟨14601434101372769723544649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19468578801830359631392865 14601434101372769723544649)
      ·
        refine ⟨10951075576029577292658487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14601434101372769723544649 10951075576029577292658487)
        ·
          refine ⟨16426613364044365938987731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10951075576029577292658487 16426613364044365938987731)
          ·
            refine ⟨24639920046066548908481597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16426613364044365938987731 24639920046066548908481597)
            ·
              refine ⟨9239970017274955840680599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24639920046066548908481597 9239970017274955840680599)
              ·
                refine ⟨13859955025912433761020899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9239970017274955840680599 13859955025912433761020899)
                ·
                  refine ⟨20789932538868650641531349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13859955025912433761020899 20789932538868650641531349)
                  ·
                    refine ⟨487264043879733999410891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 20789932538868650641531349 487264043879733999410891)
                    ·
                      rfl

theorem cell23_2846830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 3, 1, 1, 7].length) (baseStart_2846830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2846830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2846830 prefixEnd_2846830 := by exact prefixLift 2846830
  have htrace : WordTrace (prefixWord ++ tailWord_2846830) baseStart_2846830 baseEnd_2846830 := by
    simpa [prefixWord, tailWord_2846830, baseEnd_2846830] using wordTrace_append hprefix tailTrace_2846830
  have hstable : (prefixWord ++ tailWord_2846830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2846830).length < 2 ^ (prefixWord ++ tailWord_2846830).sum := by decide
  have hdescent : baseEnd_2846830 < baseStart_2846830 := by decide
  rcases family_descends (prefixWord ++ tailWord_2846830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2846877 : List Nat := [1, 4, 2, 1, 1, 3, 2, 2, 3, 4]
def baseStart_2846877 : Nat := 118140960795 + 2846877 * 2 ^ 59
def prefixEnd_2846877 : Nat := 4983230072969 + 3 ^ 40 * 2846877 * 2
def baseEnd_2846877 : Nat := 487272088409987771448319

theorem tailTrace_2846877 : CollatzResearch.WordTrace tailWord_2846877 prefixEnd_2846877 487272088409987771448319 := by
  unfold tailWord_2846877
  simp only [CollatzResearch.WordTrace]
  refine ⟨103834134507258311727722885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69222756338172207818481923 103834134507258311727722885)
  ·
    refine ⟨19468900220110933448948041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 103834134507258311727722885 19468900220110933448948041)
    ·
      refine ⟨14601675165083200086711031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19468900220110933448948041 14601675165083200086711031)
      ·
        refine ⟨21902512747624800130066547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14601675165083200086711031 21902512747624800130066547)
        ·
          refine ⟨32853769121437200195099821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21902512747624800130066547 32853769121437200195099821)
          ·
            refine ⟨12320163420538950073162433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32853769121437200195099821 12320163420538950073162433)
            ·
              refine ⟨9240122565404212554871825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12320163420538950073162433 9240122565404212554871825)
              ·
                refine ⟨6930091924053159416153869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9240122565404212554871825 6930091924053159416153869)
                ·
                  refine ⟨2598784471519934781057701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6930091924053159416153869 2598784471519934781057701)
                  ·
                    refine ⟨487272088409987771448319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2598784471519934781057701 487272088409987771448319)
                    ·
                      rfl

theorem cell23_2846877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 2, 2, 3, 4].length) (baseStart_2846877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2846877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2846877 prefixEnd_2846877 := by exact prefixLift 2846877
  have htrace : WordTrace (prefixWord ++ tailWord_2846877) baseStart_2846877 baseEnd_2846877 := by
    simpa [prefixWord, tailWord_2846877, baseEnd_2846877] using wordTrace_append hprefix tailTrace_2846877
  have hstable : (prefixWord ++ tailWord_2846877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2846877).length < 2 ^ (prefixWord ++ tailWord_2846877).sum := by decide
  have hdescent : baseEnd_2846877 < baseStart_2846877 := by decide
  rcases family_descends (prefixWord ++ tailWord_2846877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2846883 : List Nat := [1, 1, 1, 4, 1, 1, 1, 1, 2, 1, 9]
def baseStart_2846883 : Nat := 118140960795 + 2846883 * 2 ^ 59
def prefixEnd_2846883 : Nat := 4983230072969 + 3 ^ 40 * 2846883 * 2
def baseEnd_2846883 : Nat := 1461819346113890290869929

theorem tailTrace_2846883 : CollatzResearch.WordTrace tailWord_2846883 prefixEnd_2846883 1461819346113890290869929 := by
  unfold tailWord_2846883
  simp only [CollatzResearch.WordTrace]
  refine ⟨103834353345236574752441303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69222902230157716501627535 103834353345236574752441303)
  ·
    refine ⟨155751530017854862128661955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103834353345236574752441303 155751530017854862128661955)
    ·
      refine ⟨233627295026782293192992933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155751530017854862128661955 233627295026782293192992933)
      ·
        refine ⟨43805117817521679973686175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 233627295026782293192992933 43805117817521679973686175)
        ·
          refine ⟨65707676726282519960529263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43805117817521679973686175 65707676726282519960529263)
          ·
            refine ⟨98561515089423779940793895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65707676726282519960529263 98561515089423779940793895)
            ·
              refine ⟨147842272634135669911190843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 98561515089423779940793895 147842272634135669911190843)
              ·
                refine ⟨221763408951203504866786265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 147842272634135669911190843 221763408951203504866786265)
                ·
                  refine ⟨166322556713402628650089699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 221763408951203504866786265 166322556713402628650089699)
                  ·
                    refine ⟨249483835070103942975134549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 166322556713402628650089699 249483835070103942975134549)
                    ·
                      refine ⟨1461819346113890290869929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 249483835070103942975134549 1461819346113890290869929)
                      ·
                        rfl

theorem cell23_2846883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 1, 2, 1, 9].length) (baseStart_2846883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2846883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2846883 prefixEnd_2846883 := by exact prefixLift 2846883
  have htrace : WordTrace (prefixWord ++ tailWord_2846883) baseStart_2846883 baseEnd_2846883 := by
    simpa [prefixWord, tailWord_2846883, baseEnd_2846883] using wordTrace_append hprefix tailTrace_2846883
  have hstable : (prefixWord ++ tailWord_2846883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2846883).length < 2 ^ (prefixWord ++ tailWord_2846883).sum := by decide
  have hdescent : baseEnd_2846883 < baseStart_2846883 := by decide
  rcases family_descends (prefixWord ++ tailWord_2846883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2846920 : List Nat := [2, 1, 3, 1, 2, 1, 1, 4, 3, 5]
def baseStart_2846920 : Nat := 118140960795 + 2846920 * 2 ^ 59
def prefixEnd_2846920 : Nat := 4983230072969 + 3 ^ 40 * 2846920 * 2
def baseEnd_2846920 : Nat := 487279448299368882035753

theorem tailTrace_2846920 : CollatzResearch.WordTrace tailWord_2846920 prefixEnd_2846920 487279448299368882035753 := by
  unfold tailWord_2846920
  simp only [CollatzResearch.WordTrace]
  refine ⟨51917851423051265035769107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69223801897401686714358809 51917851423051265035769107)
  ·
    refine ⟨77876777134576897553653661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51917851423051265035769107 77876777134576897553653661)
    ·
      refine ⟨29203791425466336582620123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 77876777134576897553653661 29203791425466336582620123)
      ·
        refine ⟨43805687138199504873930185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29203791425466336582620123 43805687138199504873930185)
        ·
          refine ⟨32854265353649628655447639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43805687138199504873930185 32854265353649628655447639)
          ·
            refine ⟨49281398030474442983171459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32854265353649628655447639 49281398030474442983171459)
            ·
              refine ⟨73922097045711664474757189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49281398030474442983171459 73922097045711664474757189)
              ·
                refine ⟨13860393196070937089016973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 73922097045711664474757189 13860393196070937089016973)
                ·
                  refine ⟨5197647448526601408381365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13860393196070937089016973 5197647448526601408381365)
                  ·
                    refine ⟨487279448299368882035753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5197647448526601408381365 487279448299368882035753)
                    ·
                      rfl

theorem cell23_2846920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 4, 3, 5].length) (baseStart_2846920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2846920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2846920 prefixEnd_2846920 := by exact prefixLift 2846920
  have htrace : WordTrace (prefixWord ++ tailWord_2846920) baseStart_2846920 baseEnd_2846920 := by
    simpa [prefixWord, tailWord_2846920, baseEnd_2846920] using wordTrace_append hprefix tailTrace_2846920
  have hstable : (prefixWord ++ tailWord_2846920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2846920).length < 2 ^ (prefixWord ++ tailWord_2846920).sum := by decide
  have hdescent : baseEnd_2846920 < baseStart_2846920 := by decide
  rcases family_descends (prefixWord ++ tailWord_2846920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2846924 : List Nat := [2, 2, 1, 6, 1, 1, 1, 3, 6]
def baseStart_2846924 : Nat := 118140960795 + 2846924 * 2 ^ 59
def prefixEnd_2846924 : Nat := 4983230072969 + 3 ^ 40 * 2846924 * 2
def baseEnd_2846924 : Nat := 162426710980080514495249

theorem tailTrace_2846924 : CollatzResearch.WordTrace tailWord_2846924 prefixEnd_2846924 162426710980080514495249 := by
  unfold tailWord_2846924
  simp only [CollatzResearch.WordTrace]
  refine ⟨51917924369044019377341913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69223899158725359169789217 51917924369044019377341913)
  ·
    refine ⟨38938443276783014533006435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51917924369044019377341913 38938443276783014533006435)
    ·
      refine ⟨58407664915174521799509653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38938443276783014533006435 58407664915174521799509653)
      ·
        refine ⟨2737859292898805709352015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 58407664915174521799509653 2737859292898805709352015)
        ·
          refine ⟨4106788939348208564028023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2737859292898805709352015 4106788939348208564028023)
          ·
            refine ⟨6160183409022312846042035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4106788939348208564028023 6160183409022312846042035)
            ·
              refine ⟨9240275113533469269063053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6160183409022312846042035 9240275113533469269063053)
              ·
                refine ⟨3465103167575050975898645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9240275113533469269063053 3465103167575050975898645)
                ·
                  refine ⟨162426710980080514495249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3465103167575050975898645 162426710980080514495249)
                  ·
                    rfl

theorem cell23_2846924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 1, 3, 6].length) (baseStart_2846924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2846924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2846924 prefixEnd_2846924 := by exact prefixLift 2846924
  have htrace : WordTrace (prefixWord ++ tailWord_2846924) baseStart_2846924 baseEnd_2846924 := by
    simpa [prefixWord, tailWord_2846924, baseEnd_2846924] using wordTrace_append hprefix tailTrace_2846924
  have hstable : (prefixWord ++ tailWord_2846924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2846924).length < 2 ^ (prefixWord ++ tailWord_2846924).sum := by decide
  have hdescent : baseEnd_2846924 < baseStart_2846924 := by decide
  rcases family_descends (prefixWord ++ tailWord_2846924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2846927 : List Nat := [1, 1, 2, 1, 1, 3, 3, 2, 4, 3, 2]
def baseStart_2846927 : Nat := 118140960795 + 2846927 * 2 ^ 59
def prefixEnd_2846927 : Nat := 4983230072969 + 3 ^ 40 * 2846927 * 2
def baseEnd_2846927 : Nat := 1461841939262688118719727

theorem tailTrace_2846927 : CollatzResearch.WordTrace tailWord_2846927 prefixEnd_2846927 1461841939262688118719727 := by
  unfold tailWord_2846927
  simp only [CollatzResearch.WordTrace]
  refine ⟨103835958157077170267043035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69223972104718113511362023 103835958157077170267043035)
  ·
    refine ⟨155753937235615755400564553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103835958157077170267043035 155753937235615755400564553)
    ·
      refine ⟨116815452926711816550423415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 155753937235615755400564553 116815452926711816550423415)
      ·
        refine ⟨175223179390067724825635123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116815452926711816550423415 175223179390067724825635123)
        ·
          refine ⟨262834769085101587238452685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 175223179390067724825635123 262834769085101587238452685)
          ·
            refine ⟨98563038406913095214419757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 262834769085101587238452685 98563038406913095214419757)
            ·
              refine ⟨36961139402592410705407409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 98563038406913095214419757 36961139402592410705407409)
              ·
                refine ⟨27720854551944308029055557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36961139402592410705407409 27720854551944308029055557)
                ·
                  refine ⟨5197660228489557755447917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27720854551944308029055557 5197660228489557755447917)
                  ·
                    refine ⟨1949122585683584158292969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5197660228489557755447917 1949122585683584158292969)
                    ·
                      refine ⟨1461841939262688118719727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1949122585683584158292969 1461841939262688118719727)
                      ·
                        rfl

theorem cell23_2846927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 2, 4, 3, 2].length) (baseStart_2846927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2846927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2846927 prefixEnd_2846927 := by exact prefixLift 2846927
  have htrace : WordTrace (prefixWord ++ tailWord_2846927) baseStart_2846927 baseEnd_2846927 := by
    simpa [prefixWord, tailWord_2846927, baseEnd_2846927] using wordTrace_append hprefix tailTrace_2846927
  have hstable : (prefixWord ++ tailWord_2846927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2846927).length < 2 ^ (prefixWord ++ tailWord_2846927).sum := by decide
  have hdescent : baseEnd_2846927 < baseStart_2846927 := by decide
  rcases family_descends (prefixWord ++ tailWord_2846927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2846937 : List Nat := [1, 2, 1, 2, 3, 1, 5, 2, 1, 5]
def baseStart_2846937 : Nat := 118140960795 + 2846937 * 2 ^ 59
def prefixEnd_2846937 : Nat := 4983230072969 + 3 ^ 40 * 2846937 * 2
def baseEnd_2846937 : Nat := 487282358023077693198227

theorem tailTrace_2846937 : CollatzResearch.WordTrace tailWord_2846937 prefixEnd_2846937 487282358023077693198227 := by
  unfold tailWord_2846937
  simp only [CollatzResearch.WordTrace]
  refine ⟨103836322887040941974907065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69224215258027294649938043 103836322887040941974907065)
  ·
    refine ⟨77877242165280706481180299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103836322887040941974907065 77877242165280706481180299)
    ·
      refine ⟨116815863247921059721770449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77877242165280706481180299 116815863247921059721770449)
      ·
        refine ⟨87611897435940794791327837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 116815863247921059721770449 87611897435940794791327837)
        ·
          refine ⟨32854461538477798046747939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 87611897435940794791327837 32854461538477798046747939)
          ·
            refine ⟨49281692307716697070121909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32854461538477798046747939 49281692307716697070121909)
            ·
              refine ⟨4620158653848440350323929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 49281692307716697070121909 4620158653848440350323929)
              ·
                refine ⟨3465118990386330262742947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4620158653848440350323929 3465118990386330262742947)
                ·
                  refine ⟨5197678485579495394114421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3465118990386330262742947 5197678485579495394114421)
                  ·
                    refine ⟨487282358023077693198227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5197678485579495394114421 487282358023077693198227)
                    ·
                      rfl

theorem cell23_2846937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 5, 2, 1, 5].length) (baseStart_2846937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2846937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2846937 prefixEnd_2846937 := by exact prefixLift 2846937
  have htrace : WordTrace (prefixWord ++ tailWord_2846937) baseStart_2846937 baseEnd_2846937 := by
    simpa [prefixWord, tailWord_2846937, baseEnd_2846937] using wordTrace_append hprefix tailTrace_2846937
  have hstable : (prefixWord ++ tailWord_2846937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2846937).length < 2 ^ (prefixWord ++ tailWord_2846937).sum := by decide
  have hdescent : baseEnd_2846937 < baseStart_2846937 := by decide
  rcases family_descends (prefixWord ++ tailWord_2846937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2846944 : List Nat := [2, 1, 1, 3, 1, 3, 4, 1, 2, 3, 2]
def baseStart_2846944 : Nat := 118140960795 + 2846944 * 2 ^ 59
def prefixEnd_2846944 : Nat := 4983230072969 + 3 ^ 40 * 2846944 * 2
def baseEnd_2846944 : Nat := 1461850668433814552207149

theorem tailTrace_2846944 : CollatzResearch.WordTrace tailWord_2846944 prefixEnd_2846944 1461850668433814552207149 := by
  unfold tailWord_2846944
  simp only [CollatzResearch.WordTrace]
  refine ⟨51918289099007791085205943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69224385465343721446941257 51918289099007791085205943)
  ·
    refine ⟨77877433648511686627808915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51918289099007791085205943 77877433648511686627808915)
    ·
      refine ⟨116816150472767529941713373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77877433648511686627808915 116816150472767529941713373)
      ·
        refine ⟨43806056427287823728142515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 116816150472767529941713373 43806056427287823728142515)
        ·
          refine ⟨65709084640931735592213773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43806056427287823728142515 65709084640931735592213773)
          ·
            refine ⟨24640906740349400847080165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 65709084640931735592213773 24640906740349400847080165)
            ·
              refine ⟨4620170013815512658827531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24640906740349400847080165 4620170013815512658827531)
              ·
                refine ⟨6930255020723268988241297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4620170013815512658827531 6930255020723268988241297)
                ·
                  refine ⟨5197691265542451741180973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6930255020723268988241297 5197691265542451741180973)
                  ·
                    refine ⟨1949134224578419402942865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5197691265542451741180973 1949134224578419402942865)
                    ·
                      refine ⟨1461850668433814552207149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1949134224578419402942865 1461850668433814552207149)
                      ·
                        rfl

theorem cell23_2846944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 4, 1, 2, 3, 2].length) (baseStart_2846944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2846944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2846944 prefixEnd_2846944 := by exact prefixLift 2846944
  have htrace : WordTrace (prefixWord ++ tailWord_2846944) baseStart_2846944 baseEnd_2846944 := by
    simpa [prefixWord, tailWord_2846944, baseEnd_2846944] using wordTrace_append hprefix tailTrace_2846944
  have hstable : (prefixWord ++ tailWord_2846944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2846944).length < 2 ^ (prefixWord ++ tailWord_2846944).sum := by decide
  have hdescent : baseEnd_2846944 < baseStart_2846944 := by decide
  rcases family_descends (prefixWord ++ tailWord_2846944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2846954 : List Nat := [3, 1, 3, 1, 1, 2, 5, 1, 1, 5]
def baseStart_2846954 : Nat := 118140960795 + 2846954 * 2 ^ 59
def prefixEnd_2846954 : Nat := 4983230072969 + 3 ^ 40 * 2846954 * 2
def baseEnd_2846954 : Nat := 487285267746786504360701

theorem tailTrace_2846954 : CollatzResearch.WordTrace tailWord_2846954 prefixEnd_2846954 487285267746786504360701 := by
  unfold tailWord_2846954
  simp only [CollatzResearch.WordTrace]
  refine ⟨25959235731994838469568979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69224628618652902585517277 25959235731994838469568979)
  ·
    refine ⟨38938853597992257704353469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25959235731994838469568979 38938853597992257704353469)
    ·
      refine ⟨14602070099247096639132551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38938853597992257704353469 14602070099247096639132551)
      ·
        refine ⟨21903105148870644958698827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14602070099247096639132551 21903105148870644958698827)
        ·
          refine ⟨32854657723305967438048241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21903105148870644958698827 32854657723305967438048241)
          ·
            refine ⟨24640993292479475578536181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32854657723305967438048241 24640993292479475578536181)
            ·
              refine ⟨2310093121169950835487767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 24640993292479475578536181 2310093121169950835487767)
              ·
                refine ⟨3465139681754926253231651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2310093121169950835487767 3465139681754926253231651)
                ·
                  refine ⟨5197709522632389379847477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3465139681754926253231651 5197709522632389379847477)
                  ·
                    refine ⟨487285267746786504360701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5197709522632389379847477 487285267746786504360701)
                    ·
                      rfl

theorem cell23_2846954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 5, 1, 1, 5].length) (baseStart_2846954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2846954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2846954 prefixEnd_2846954 := by exact prefixLift 2846954
  have htrace : WordTrace (prefixWord ++ tailWord_2846954) baseStart_2846954 baseEnd_2846954 := by
    simpa [prefixWord, tailWord_2846954, baseEnd_2846954] using wordTrace_append hprefix tailTrace_2846954
  have hstable : (prefixWord ++ tailWord_2846954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2846954).length < 2 ^ (prefixWord ++ tailWord_2846954).sum := by decide
  have hdescent : baseEnd_2846954 < baseStart_2846954 := by decide
  rcases family_descends (prefixWord ++ tailWord_2846954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2846977 : List Nat := [1, 2, 4, 1, 1, 2, 1, 1, 5, 2, 3]
def baseStart_2846977 : Nat := 118140960795 + 2846977 * 2 ^ 59
def prefixEnd_2846977 : Nat := 4983230072969 + 3 ^ 40 * 2846977 * 2
def baseEnd_2846977 : Nat := 1461867613295412923094497

theorem tailTrace_2846977 : CollatzResearch.WordTrace tailWord_2846977 prefixEnd_2846977 1461867613295412923094497 := by
  unfold tailWord_2846977
  simp only [CollatzResearch.WordTrace]
  refine ⟨103837781806896028806363185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69225187871264019204242123 103837781806896028806363185)
  ·
    refine ⟨77878336355172021604772389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103837781806896028806363185 77878336355172021604772389)
    ·
      refine ⟨14602188066594754050894823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 77878336355172021604772389 14602188066594754050894823)
      ·
        refine ⟨21903282099892131076342235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14602188066594754050894823 21903282099892131076342235)
        ·
          refine ⟨32854923149838196614513353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21903282099892131076342235 32854923149838196614513353)
          ·
            refine ⟨24641192362378647460885015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32854923149838196614513353 24641192362378647460885015)
            ·
              refine ⟨36961788543567971191327523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24641192362378647460885015 36961788543567971191327523)
              ·
                refine ⟨55442682815351956786991285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36961788543567971191327523 55442682815351956786991285)
                ·
                  refine ⟨5197751513939245948780433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 55442682815351956786991285 5197751513939245948780433)
                  ·
                    refine ⟨3898313635454434461585325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5197751513939245948780433 3898313635454434461585325)
                    ·
                      refine ⟨1461867613295412923094497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3898313635454434461585325 1461867613295412923094497)
                      ·
                        rfl

theorem cell23_2846977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 1, 5, 2, 3].length) (baseStart_2846977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2846977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2846977 prefixEnd_2846977 := by exact prefixLift 2846977
  have htrace : WordTrace (prefixWord ++ tailWord_2846977) baseStart_2846977 baseEnd_2846977 := by
    simpa [prefixWord, tailWord_2846977, baseEnd_2846977] using wordTrace_append hprefix tailTrace_2846977
  have hstable : (prefixWord ++ tailWord_2846977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2846977).length < 2 ^ (prefixWord ++ tailWord_2846977).sum := by decide
  have hdescent : baseEnd_2846977 < baseStart_2846977 := by decide
  rcases family_descends (prefixWord ++ tailWord_2846977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2846984 : List Nat := [2, 1, 3, 2, 3, 1, 2, 3, 2, 4]
def baseStart_2846984 : Nat := 118140960795 + 2846984 * 2 ^ 59
def prefixEnd_2846984 : Nat := 4983230072969 + 3 ^ 40 * 2846984 * 2
def baseEnd_2846984 : Nat := 487290402553331465235655

theorem tailTrace_2846984 : CollatzResearch.WordTrace tailWord_2846984 prefixEnd_2846984 487290402553331465235655 := by
  unfold tailWord_2846984
  simp only [CollatzResearch.WordTrace]
  refine ⟨51919018558935334500934003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69225358078580446001245337 51919018558935334500934003)
  ·
    refine ⟨77878527838403001751401005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51919018558935334500934003 77878527838403001751401005)
    ·
      refine ⟨29204447939401125656775377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 77878527838403001751401005 29204447939401125656775377)
      ·
        refine ⟨21903335954550844242581533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29204447939401125656775377 21903335954550844242581533)
        ·
          refine ⟨8213750982956566590968075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21903335954550844242581533 8213750982956566590968075)
          ·
            refine ⟨12320626474434849886452113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8213750982956566590968075 12320626474434849886452113)
            ·
              refine ⟨9240469855826137414839085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12320626474434849886452113 9240469855826137414839085)
              ·
                refine ⟨3465176195934801530564657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9240469855826137414839085 3465176195934801530564657)
                ·
                  refine ⟨2598882146951101147923493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3465176195934801530564657 2598882146951101147923493)
                  ·
                    refine ⟨487290402553331465235655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2598882146951101147923493 487290402553331465235655)
                    ·
                      rfl

theorem cell23_2846984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 2, 3, 2, 4].length) (baseStart_2846984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2846984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2846984 prefixEnd_2846984 := by exact prefixLift 2846984
  have htrace : WordTrace (prefixWord ++ tailWord_2846984) baseStart_2846984 baseEnd_2846984 := by
    simpa [prefixWord, tailWord_2846984, baseEnd_2846984] using wordTrace_append hprefix tailTrace_2846984
  have hstable : (prefixWord ++ tailWord_2846984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2846984).length < 2 ^ (prefixWord ++ tailWord_2846984).sum := by decide
  have hdescent : baseEnd_2846984 < baseStart_2846984 := by decide
  rcases family_descends (prefixWord ++ tailWord_2846984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2846987 : List Nat := [1, 1, 1, 1, 5, 2, 4, 1, 1, 2, 4]
def baseStart_2846987 : Nat := 118140960795 + 2846987 * 2 ^ 59
def prefixEnd_2846987 : Nat := 4983230072969 + 3 ^ 40 * 2846987 * 2
def baseEnd_2846987 : Nat := 1461872748101957883969451

theorem tailTrace_2846987 : CollatzResearch.WordTrace tailWord_2846987 prefixEnd_2846987 1461872748101957883969451 := by
  unfold tailWord_2846987
  simp only [CollatzResearch.WordTrace]
  refine ⟨103838146536859800514227215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69225431024573200342818143 103838146536859800514227215)
  ·
    refine ⟨155757219805289700771340823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103838146536859800514227215 155757219805289700771340823)
    ·
      refine ⟨233635829707934551157011235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155757219805289700771340823 233635829707934551157011235)
      ·
        refine ⟨350453744561901826735516853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 233635829707934551157011235 350453744561901826735516853)
        ·
          refine ⟨32855038552678296256454705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 350453744561901826735516853 32855038552678296256454705)
          ·
            refine ⟨24641278914508722192341029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32855038552678296256454705 24641278914508722192341029)
            ·
              refine ⟨4620239796470385411063943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24641278914508722192341029 4620239796470385411063943)
              ·
                refine ⟨6930359694705578116595915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4620239796470385411063943 6930359694705578116595915)
                ·
                  refine ⟨10395539542058367174893873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6930359694705578116595915 10395539542058367174893873)
                  ·
                    refine ⟨7796654656543775381170405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10395539542058367174893873 7796654656543775381170405)
                    ·
                      refine ⟨1461872748101957883969451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7796654656543775381170405 1461872748101957883969451)
                      ·
                        rfl

theorem cell23_2846987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 4, 1, 1, 2, 4].length) (baseStart_2846987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2846987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2846987 prefixEnd_2846987 := by exact prefixLift 2846987
  have htrace : WordTrace (prefixWord ++ tailWord_2846987) baseStart_2846987 baseEnd_2846987 := by
    simpa [prefixWord, tailWord_2846987, baseEnd_2846987] using wordTrace_append hprefix tailTrace_2846987
  have hstable : (prefixWord ++ tailWord_2846987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2846987).length < 2 ^ (prefixWord ++ tailWord_2846987).sum := by decide
  have hdescent : baseEnd_2846987 < baseStart_2846987 := by decide
  rcases family_descends (prefixWord ++ tailWord_2846987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2847008 : List Nat := [2, 1, 1, 5, 2, 1, 1, 5, 1, 2, 2]
def baseStart_2847008 : Nat := 118140960795 + 2847008 * 2 ^ 59
def prefixEnd_2847008 : Nat := 4983230072969 + 3 ^ 40 * 2847008 * 2
def baseEnd_2847008 : Nat := 1461883531195702301806855

theorem tailTrace_2847008 : CollatzResearch.WordTrace tailWord_2847008 prefixEnd_2847008 1461883531195702301806855 := by
  unfold tailWord_2847008
  simp only [CollatzResearch.WordTrace]
  refine ⟨51919456234891860550370839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69225941646522480733827785 51919456234891860550370839)
  ·
    refine ⟨77879184352337790825556259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51919456234891860550370839 77879184352337790825556259)
    ·
      refine ⟨116818776528506686238334389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77879184352337790825556259 116818776528506686238334389)
      ·
        refine ⟨10951760299547501834843849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 116818776528506686238334389 10951760299547501834843849)
        ·
          refine ⟨8213820224660626376132887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10951760299547501834843849 8213820224660626376132887)
          ·
            refine ⟨12320730336990939564199331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8213820224660626376132887 12320730336990939564199331)
            ·
              refine ⟨18481095505486409346298997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12320730336990939564199331 18481095505486409346298997)
              ·
                refine ⟨1732602703639350876215531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 18481095505486409346298997 1732602703639350876215531)
                ·
                  refine ⟨2598904055459026314323297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1732602703639350876215531 2598904055459026314323297)
                  ·
                    refine ⟨1949178041594269735742473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2598904055459026314323297 1949178041594269735742473)
                    ·
                      refine ⟨1461883531195702301806855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1949178041594269735742473 1461883531195702301806855)
                      ·
                        rfl

theorem cell23_2847008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 1, 5, 1, 2, 2].length) (baseStart_2847008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2847008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2847008 prefixEnd_2847008 := by exact prefixLift 2847008
  have htrace : WordTrace (prefixWord ++ tailWord_2847008) baseStart_2847008 baseEnd_2847008 := by
    simpa [prefixWord, tailWord_2847008, baseEnd_2847008] using wordTrace_append hprefix tailTrace_2847008
  have hstable : (prefixWord ++ tailWord_2847008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2847008).length < 2 ^ (prefixWord ++ tailWord_2847008).sum := by decide
  have hdescent : baseEnd_2847008 < baseStart_2847008 := by decide
  rcases family_descends (prefixWord ++ tailWord_2847008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2847018 : List Nat := [3, 1, 4, 2, 2, 2, 1, 2, 2, 4]
def baseStart_2847018 : Nat := 118140960795 + 2847018 * 2 ^ 59
def prefixEnd_2847018 : Nat := 4983230072969 + 3 ^ 40 * 2847018 * 2
def baseEnd_2847018 : Nat := 487296222000749087560603

theorem tailTrace_2847018 : CollatzResearch.WordTrace tailWord_2847018 prefixEnd_2847018 487296222000749087560603 := by
  unfold tailWord_2847018
  simp only [CollatzResearch.WordTrace]
  refine ⟨25959819299936873202151427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69226184799831661872403805 25959819299936873202151427)
  ·
    refine ⟨38939728949905309803227141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25959819299936873202151427 38939728949905309803227141)
    ·
      refine ⟨7301199178107245588105089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 38939728949905309803227141 7301199178107245588105089)
      ·
        refine ⟨5475899383580434191078817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7301199178107245588105089 5475899383580434191078817)
        ·
          refine ⟨4106924537685325643309113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5475899383580434191078817 4106924537685325643309113)
          ·
            refine ⟨3080193403263994232481835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4106924537685325643309113 3080193403263994232481835)
            ·
              refine ⟨4620290104895991348722753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3080193403263994232481835 4620290104895991348722753)
              ·
                refine ⟨3465217578671993511542065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4620290104895991348722753 3465217578671993511542065)
                ·
                  refine ⟨2598913184003995133656549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3465217578671993511542065 2598913184003995133656549)
                  ·
                    refine ⟨487296222000749087560603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2598913184003995133656549 487296222000749087560603)
                    ·
                      rfl

theorem cell23_2847018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 2, 1, 2, 2, 4].length) (baseStart_2847018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2847018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2847018 prefixEnd_2847018 := by exact prefixLift 2847018
  have htrace : WordTrace (prefixWord ++ tailWord_2847018) baseStart_2847018 baseEnd_2847018 := by
    simpa [prefixWord, tailWord_2847018, baseEnd_2847018] using wordTrace_append hprefix tailTrace_2847018
  have hstable : (prefixWord ++ tailWord_2847018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2847018).length < 2 ^ (prefixWord ++ tailWord_2847018).sum := by decide
  have hdescent : baseEnd_2847018 < baseStart_2847018 := by decide
  rcases family_descends (prefixWord ++ tailWord_2847018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2847024 : List Nat := [2, 1, 1, 1, 2, 2, 2, 6, 2, 1, 3]
def baseStart_2847024 : Nat := 118140960795 + 2847024 * 2 ^ 59
def prefixEnd_2847024 : Nat := 4983230072969 + 3 ^ 40 * 2847024 * 2
def baseEnd_2847024 : Nat := 1461891746886174239206781

theorem tailTrace_2847024 : CollatzResearch.WordTrace tailWord_2847024 prefixEnd_2847024 1461891746886174239206781 := by
  unfold tailWord_2847024
  simp only [CollatzResearch.WordTrace]
  refine ⟨51919748018862877916662063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69226330691817170555549417 51919748018862877916662063)
  ·
    refine ⟨77879622028294316874993095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51919748018862877916662063 77879622028294316874993095)
    ·
      refine ⟨116819433042441475312489643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77879622028294316874993095 116819433042441475312489643)
      ·
        refine ⟨175229149563662212968734465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116819433042441475312489643 175229149563662212968734465)
        ·
          refine ⟨131421862172746659726550849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 175229149563662212968734465 131421862172746659726550849)
          ·
            refine ⟨98566396629559994794913137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 131421862172746659726550849 98566396629559994794913137)
            ·
              refine ⟨73924797472169996096184853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 98566396629559994794913137 73924797472169996096184853)
              ·
                refine ⟨3465224881507968567008665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 73924797472169996096184853 3465224881507968567008665)
                ·
                  refine ⟨2598918661130976425256499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3465224881507968567008665 2598918661130976425256499)
                  ·
                    refine ⟨3898377991696464637884749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2598918661130976425256499 3898377991696464637884749)
                    ·
                      refine ⟨1461891746886174239206781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3898377991696464637884749 1461891746886174239206781)
                      ·
                        rfl

theorem cell23_2847024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 6, 2, 1, 3].length) (baseStart_2847024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2847024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2847024 prefixEnd_2847024 := by exact prefixLift 2847024
  have htrace : WordTrace (prefixWord ++ tailWord_2847024) baseStart_2847024 baseEnd_2847024 := by
    simpa [prefixWord, tailWord_2847024, baseEnd_2847024] using wordTrace_append hprefix tailTrace_2847024
  have hstable : (prefixWord ++ tailWord_2847024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2847024).length < 2 ^ (prefixWord ++ tailWord_2847024).sum := by decide
  have hdescent : baseEnd_2847024 < baseStart_2847024 := by decide
  rcases family_descends (prefixWord ++ tailWord_2847024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2847040 : List Nat := [2, 1, 1, 2, 2, 1, 2, 3, 1, 8]
def baseStart_2847040 : Nat := 118140960795 + 2847040 * 2 ^ 59
def prefixEnd_2847040 : Nat := 4983230072969 + 3 ^ 40 * 2847040 * 2
def baseEnd_2847040 : Nat := 487299987525548725535569

theorem tailTrace_2847040 : CollatzResearch.WordTrace tailWord_2847040 prefixEnd_2847040 487299987525548725535569 := by
  unfold tailWord_2847040
  simp only [CollatzResearch.WordTrace]
  refine ⟨51920039802833895282953287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69226719737111860377271049 51920039802833895282953287)
  ·
    refine ⟨77880059704250842924429931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51920039802833895282953287 77880059704250842924429931)
    ·
      refine ⟨116820089556376264386644897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77880059704250842924429931 116820089556376264386644897)
      ·
        refine ⟨87615067167282198289983673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 116820089556376264386644897 87615067167282198289983673)
        ·
          refine ⟨65711300375461648717487755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87615067167282198289983673 65711300375461648717487755)
          ·
            refine ⟨98566950563192473076231633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65711300375461648717487755 98566950563192473076231633)
            ·
              refine ⟨73925212922394354807173725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 98566950563192473076231633 73925212922394354807173725)
              ·
                refine ⟨27721954845897883052690147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 73925212922394354807173725 27721954845897883052690147)
                ·
                  refine ⟨41582932268846824579035221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27721954845897883052690147 41582932268846824579035221)
                  ·
                    refine ⟨487299987525548725535569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 41582932268846824579035221 487299987525548725535569)
                    ·
                      rfl

theorem cell23_2847040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 3, 1, 8].length) (baseStart_2847040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2847040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2847040 prefixEnd_2847040 := by exact prefixLift 2847040
  have htrace : WordTrace (prefixWord ++ tailWord_2847040) baseStart_2847040 baseEnd_2847040 := by
    simpa [prefixWord, tailWord_2847040, baseEnd_2847040] using wordTrace_append hprefix tailTrace_2847040
  have hstable : (prefixWord ++ tailWord_2847040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2847040).length < 2 ^ (prefixWord ++ tailWord_2847040).sum := by decide
  have hdescent : baseEnd_2847040 < baseStart_2847040 := by decide
  rcases family_descends (prefixWord ++ tailWord_2847040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2847081 : List Nat := [1, 2, 1, 1, 1, 3, 4, 4, 2, 2, 2]
def baseStart_2847081 : Nat := 118140960795 + 2847081 * 2 ^ 59
def prefixEnd_2847081 : Nat := 4983230072969 + 3 ^ 40 * 2847081 * 2
def baseEnd_2847081 : Nat := 1461921015283480516194019

theorem tailTrace_2847081 : CollatzResearch.WordTrace tailWord_2847081 prefixEnd_2847081 1461921015283480516194019 := by
  unfold tailWord_2847081
  simp only [CollatzResearch.WordTrace]
  refine ⟨103841574998519254568149097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69227716665679503045432731 103841574998519254568149097)
  ·
    refine ⟨77881181248889440926111823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103841574998519254568149097 77881181248889440926111823)
    ·
      refine ⟨116821771873334161389167735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77881181248889440926111823 116821771873334161389167735)
      ·
        refine ⟨175232657810001242083751603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116821771873334161389167735 175232657810001242083751603)
        ·
          refine ⟨262848986715001863125627405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 175232657810001242083751603 262848986715001863125627405)
          ·
            refine ⟨98568370018125698672110277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 262848986715001863125627405 98568370018125698672110277)
            ·
              refine ⟨18481569378398568501020677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 98568370018125698672110277 18481569378398568501020677)
              ·
                refine ⟨3465294258449731593941377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18481569378398568501020677 3465294258449731593941377)
                ·
                  refine ⟨2598970693837298695456033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3465294258449731593941377 2598970693837298695456033)
                  ·
                    refine ⟨1949228020377974021592025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2598970693837298695456033 1949228020377974021592025)
                    ·
                      refine ⟨1461921015283480516194019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1949228020377974021592025 1461921015283480516194019)
                      ·
                        rfl

theorem cell23_2847081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 4, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 4, 4, 2, 2, 2].length) (baseStart_2847081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2847081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2847081 prefixEnd_2847081 := by exact prefixLift 2847081
  have htrace : WordTrace (prefixWord ++ tailWord_2847081) baseStart_2847081 baseEnd_2847081 := by
    simpa [prefixWord, tailWord_2847081, baseEnd_2847081] using wordTrace_append hprefix tailTrace_2847081
  have hstable : (prefixWord ++ tailWord_2847081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2847081).length < 2 ^ (prefixWord ++ tailWord_2847081).sum := by decide
  have hdescent : baseEnd_2847081 < baseStart_2847081 := by decide
  rcases family_descends (prefixWord ++ tailWord_2847081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2847097 : List Nat := [1, 2, 1, 3, 2, 1, 1, 3, 1, 5, 3]
def baseStart_2847097 : Nat := 118140960795 + 2847097 * 2 ^ 59
def prefixEnd_2847097 : Nat := 4983230072969 + 3 ^ 40 * 2847097 * 2
def baseEnd_2847097 : Nat := 1461929230973952453593945

theorem tailTrace_2847097 : CollatzResearch.WordTrace tailWord_2847097 prefixEnd_2847097 1461929230973952453593945 := by
  unfold tailWord_2847097
  simp only [CollatzResearch.WordTrace]
  refine ⟨103842158566461289300731545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69228105710974192867154363 103842158566461289300731545)
  ·
    refine ⟨77881618924845966975548659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103842158566461289300731545 77881618924845966975548659)
    ·
      refine ⟨116822428387268950463322989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77881618924845966975548659 116822428387268950463322989)
      ·
        refine ⟨43808410645225856423746121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 116822428387268950463322989 43808410645225856423746121)
        ·
          refine ⟨32856307983919392317809591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43808410645225856423746121 32856307983919392317809591)
          ·
            refine ⟨49284461975879088476714387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32856307983919392317809591 49284461975879088476714387)
            ·
              refine ⟨73926692963818632715071581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49284461975879088476714387 73926692963818632715071581)
              ·
                refine ⟨27722509861431987268151843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 73926692963818632715071581 27722509861431987268151843)
                ·
                  refine ⟨41583764792147980902227765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27722509861431987268151843 41583764792147980902227765)
                  ·
                    refine ⟨3898477949263873209583853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 41583764792147980902227765 3898477949263873209583853)
                    ·
                      refine ⟨1461929230973952453593945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3898477949263873209583853 1461929230973952453593945)
                      ·
                        rfl

theorem cell23_2847097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 3, 1, 5, 3].length) (baseStart_2847097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2847097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2847097 prefixEnd_2847097 := by exact prefixLift 2847097
  have htrace : WordTrace (prefixWord ++ tailWord_2847097) baseStart_2847097 baseEnd_2847097 := by
    simpa [prefixWord, tailWord_2847097, baseEnd_2847097] using wordTrace_append hprefix tailTrace_2847097
  have hstable : (prefixWord ++ tailWord_2847097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2847097).length < 2 ^ (prefixWord ++ tailWord_2847097).sum := by decide
  have hdescent : baseEnd_2847097 < baseStart_2847097 := by decide
  rcases family_descends (prefixWord ++ tailWord_2847097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2847127 : List Nat := [1, 1, 3, 3, 1, 1, 3, 2, 1, 2, 5]
def baseStart_2847127 : Nat := 118140960795 + 2847127 * 2 ^ 59
def prefixEnd_2847127 : Nat := 4983230072969 + 3 ^ 40 * 2847127 * 2
def baseEnd_2847127 : Nat := 1461944635393587336218807

theorem tailTrace_2847127 : CollatzResearch.WordTrace tailWord_2847127 prefixEnd_2847127 1461944635393587336218807 := by
  unfold tailWord_2847127
  simp only [CollatzResearch.WordTrace]
  refine ⟨103843252756352604424323635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69228835170901736282882423 103843252756352604424323635)
  ·
    refine ⟨155764879134528906636485453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103843252756352604424323635 155764879134528906636485453)
    ·
      refine ⟨58411829675448339988682045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 155764879134528906636485453 58411829675448339988682045)
      ·
        refine ⟨21904436128293127495755767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58411829675448339988682045 21904436128293127495755767)
        ·
          refine ⟨32856654192439691243633651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21904436128293127495755767 32856654192439691243633651)
          ·
            refine ⟨49284981288659536865450477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32856654192439691243633651 49284981288659536865450477)
            ·
              refine ⟨18481867983247326324543929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49284981288659536865450477 18481867983247326324543929)
              ·
                refine ⟨13861400987435494743407947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18481867983247326324543929 13861400987435494743407947)
                ·
                  refine ⟨20792101481153242115111921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13861400987435494743407947 20792101481153242115111921)
                  ·
                    refine ⟨15594076110864931586333941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20792101481153242115111921 15594076110864931586333941)
                    ·
                      refine ⟨1461944635393587336218807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15594076110864931586333941 1461944635393587336218807)
                      ·
                        rfl

theorem cell23_2847127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 3, 2, 1, 2, 5].length) (baseStart_2847127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2847127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2847127 prefixEnd_2847127 := by exact prefixLift 2847127
  have htrace : WordTrace (prefixWord ++ tailWord_2847127) baseStart_2847127 baseEnd_2847127 := by
    simpa [prefixWord, tailWord_2847127, baseEnd_2847127] using wordTrace_append hprefix tailTrace_2847127
  have hstable : (prefixWord ++ tailWord_2847127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2847127).length < 2 ^ (prefixWord ++ tailWord_2847127).sum := by decide
  have hdescent : baseEnd_2847127 < baseStart_2847127 := by decide
  rcases family_descends (prefixWord ++ tailWord_2847127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2847231 : List Nat := [1, 1, 2, 2, 1, 2, 4, 3, 2, 3, 2]
def baseStart_2847231 : Nat := 118140960795 + 2847231 * 2 ^ 59
def prefixEnd_2847231 : Nat := 4983230072969 + 3 ^ 40 * 2847231 * 2
def baseEnd_2847231 : Nat := 1461998037381654929318329

theorem tailTrace_2847231 : CollatzResearch.WordTrace tailWord_2847231 prefixEnd_2847231 1461998037381654929318329 := by
  unfold tailWord_2847231
  simp only [CollatzResearch.WordTrace]
  refine ⟨103847045947975830186109547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69231363965317220124073031 103847045947975830186109547)
  ·
    refine ⟨155770568921963745279164321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103847045947975830186109547 155770568921963745279164321)
    ·
      refine ⟨116827926691472808959373241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 155770568921963745279164321 116827926691472808959373241)
      ·
        refine ⟨87620945018604606719529931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 116827926691472808959373241 87620945018604606719529931)
        ·
          refine ⟨131431417527906910079294897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87620945018604606719529931 131431417527906910079294897)
          ·
            refine ⟨98573563145930182559471173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 131431417527906910079294897 98573563145930182559471173)
            ·
              refine ⟨18482543089861909229900845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 98573563145930182559471173 18482543089861909229900845)
              ·
                refine ⟨6930953658698215961212817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18482543089861909229900845 6930953658698215961212817)
                ·
                  refine ⟨5198215244023661970909613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6930953658698215961212817 5198215244023661970909613)
                  ·
                    refine ⟨1949330716508873239091105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5198215244023661970909613 1949330716508873239091105)
                    ·
                      refine ⟨1461998037381654929318329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1949330716508873239091105 1461998037381654929318329)
                      ·
                        rfl

theorem cell23_2847231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 4, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 4, 3, 2, 3, 2].length) (baseStart_2847231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2847231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2847231 prefixEnd_2847231 := by exact prefixLift 2847231
  have htrace : WordTrace (prefixWord ++ tailWord_2847231) baseStart_2847231 baseEnd_2847231 := by
    simpa [prefixWord, tailWord_2847231, baseEnd_2847231] using wordTrace_append hprefix tailTrace_2847231
  have hstable : (prefixWord ++ tailWord_2847231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2847231).length < 2 ^ (prefixWord ++ tailWord_2847231).sum := by decide
  have hdescent : baseEnd_2847231 < baseStart_2847231 := by decide
  rcases family_descends (prefixWord ++ tailWord_2847231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2847278 : List Nat := [4, 1, 3, 1, 3, 1, 1, 1, 3, 1, 4]
def baseStart_2847278 : Nat := 118140960795 + 2847278 * 2 ^ 59
def prefixEnd_2847278 : Nat := 4983230072969 + 3 ^ 40 * 2847278 * 2
def baseEnd_2847278 : Nat := 1462022170972416245430613

theorem tailTrace_2847278 : CollatzResearch.WordTrace tailWord_2847278 prefixEnd_2847278 1462022170972416245430613 := by
  unfold tailWord_2847278
  simp only [CollatzResearch.WordTrace]
  refine ⟨12981095022350694651633811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 69232506785870371475380325 12981095022350694651633811)
  ·
    refine ⟨19471642533526041977450717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12981095022350694651633811 19471642533526041977450717)
    ·
      refine ⟨7301865950072265741544019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19471642533526041977450717 7301865950072265741544019)
      ·
        refine ⟨10952798925108398612316029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7301865950072265741544019 10952798925108398612316029)
        ·
          refine ⟨4107299596915649479618511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10952798925108398612316029 4107299596915649479618511)
          ·
            refine ⟨6160949395373474219427767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4107299596915649479618511 6160949395373474219427767)
            ·
              refine ⟨9241424093060211329141651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6160949395373474219427767 9241424093060211329141651)
              ·
                refine ⟨13862136139590316993712477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9241424093060211329141651 13862136139590316993712477)
                ·
                  refine ⟨5198301052346368872642179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13862136139590316993712477 5198301052346368872642179)
                  ·
                    refine ⟨7797451578519553308963269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5198301052346368872642179 7797451578519553308963269)
                    ·
                      refine ⟨1462022170972416245430613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7797451578519553308963269 1462022170972416245430613)
                      ·
                        rfl

theorem cell23_2847278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 1, 1, 3, 1, 4].length) (baseStart_2847278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2847278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2847278 prefixEnd_2847278 := by exact prefixLift 2847278
  have htrace : WordTrace (prefixWord ++ tailWord_2847278) baseStart_2847278 baseEnd_2847278 := by
    simpa [prefixWord, tailWord_2847278, baseEnd_2847278] using wordTrace_append hprefix tailTrace_2847278
  have hstable : (prefixWord ++ tailWord_2847278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2847278).length < 2 ^ (prefixWord ++ tailWord_2847278).sum := by decide
  have hdescent : baseEnd_2847278 < baseStart_2847278 := by decide
  rcases family_descends (prefixWord ++ tailWord_2847278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2847295 : List Nat := [1, 1, 2, 2, 3, 2, 2, 5, 1, 2, 2]
def baseStart_2847295 : Nat := 118140960795 + 2847295 * 2 ^ 59
def prefixEnd_2847295 : Nat := 4983230072969 + 3 ^ 40 * 2847295 * 2
def baseEnd_2847295 : Nat := 1462030900143542678918035

theorem tailTrace_2847295 : CollatzResearch.WordTrace tailWord_2847295 prefixEnd_2847295 1462030900143542678918035 := by
  unfold tailWord_2847295
  simp only [CollatzResearch.WordTrace]
  refine ⟨103849380219743969116439339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69232920146495979410959559 103849380219743969116439339)
  ·
    refine ⟨155774070329615953674659009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103849380219743969116439339 155774070329615953674659009)
    ·
      refine ⟨116830552747211965255994257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 155774070329615953674659009 116830552747211965255994257)
      ·
        refine ⟨87622914560408973941995693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 116830552747211965255994257 87622914560408973941995693)
        ·
          refine ⟨32858592960153365228248385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 87622914560408973941995693 32858592960153365228248385)
          ·
            refine ⟨24643944720115023921186289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32858592960153365228248385 24643944720115023921186289)
            ·
              refine ⟨18482958540086267940889717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24643944720115023921186289 18482958540086267940889717)
              ·
                refine ⟨1732777363133087619458411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 18482958540086267940889717 1732777363133087619458411)
                ·
                  refine ⟨2599166044699631429187617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1732777363133087619458411 2599166044699631429187617)
                  ·
                    refine ⟨1949374533524723571890713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2599166044699631429187617 1949374533524723571890713)
                    ·
                      refine ⟨1462030900143542678918035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1949374533524723571890713 1462030900143542678918035)
                      ·
                        rfl

theorem cell23_2847295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 2, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 2, 5, 1, 2, 2].length) (baseStart_2847295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2847295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2847295 prefixEnd_2847295 := by exact prefixLift 2847295
  have htrace : WordTrace (prefixWord ++ tailWord_2847295) baseStart_2847295 baseEnd_2847295 := by
    simpa [prefixWord, tailWord_2847295, baseEnd_2847295] using wordTrace_append hprefix tailTrace_2847295
  have hstable : (prefixWord ++ tailWord_2847295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2847295).length < 2 ^ (prefixWord ++ tailWord_2847295).sum := by decide
  have hdescent : baseEnd_2847295 < baseStart_2847295 := by decide
  rcases family_descends (prefixWord ++ tailWord_2847295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2847311 : List Nat := [1, 1, 2, 1, 1, 2, 4, 3, 4, 1, 3]
def baseStart_2847311 : Nat := 118140960795 + 2847311 * 2 ^ 59
def prefixEnd_2847311 : Nat := 4983230072969 + 3 ^ 40 * 2847311 * 2
def baseEnd_2847311 : Nat := 1462039115834014616317961

theorem tailTrace_2847311 : CollatzResearch.WordTrace tailWord_2847311 prefixEnd_2847311 1462039115834014616317961 := by
  unfold tailWord_2847311
  simp only [CollatzResearch.WordTrace]
  refine ⟨103849963787686003849021787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69233309191790669232681191 103849963787686003849021787)
  ·
    refine ⟨155774945681529005773532681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103849963787686003849021787 155774945681529005773532681)
    ·
      refine ⟨116831209261146754330149511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 155774945681529005773532681 116831209261146754330149511)
      ·
        refine ⟨175246813891720131495224267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116831209261146754330149511 175246813891720131495224267)
        ·
          refine ⟨262870220837580197242836401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 175246813891720131495224267 262870220837580197242836401)
          ·
            refine ⟨197152665628185147932127301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 262870220837580197242836401 197152665628185147932127301)
            ·
              refine ⟨36966124805284715237273869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 197152665628185147932127301 36966124805284715237273869)
              ·
                refine ⟨13862296801981768213977701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36966124805284715237273869 13862296801981768213977701)
                ·
                  refine ⟨2599180650371581540120819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13862296801981768213977701 2599180650371581540120819)
                  ·
                    refine ⟨3898770975557372310181229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2599180650371581540120819 3898770975557372310181229)
                    ·
                      refine ⟨1462039115834014616317961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3898770975557372310181229 1462039115834014616317961)
                      ·
                        rfl

theorem cell23_2847311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 3, 4, 1, 3].length) (baseStart_2847311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2847311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2847311 prefixEnd_2847311 := by exact prefixLift 2847311
  have htrace : WordTrace (prefixWord ++ tailWord_2847311) baseStart_2847311 baseEnd_2847311 := by
    simpa [prefixWord, tailWord_2847311, baseEnd_2847311] using wordTrace_append hprefix tailTrace_2847311
  have hstable : (prefixWord ++ tailWord_2847311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2847311).length < 2 ^ (prefixWord ++ tailWord_2847311).sum := by decide
  have hdescent : baseEnd_2847311 < baseStart_2847311 := by decide
  rcases family_descends (prefixWord ++ tailWord_2847311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2847314 : List Nat := [3, 2, 2, 1, 2, 1, 1, 1, 1, 9]
def baseStart_2847314 : Nat := 118140960795 + 2847314 * 2 ^ 59
def prefixEnd_2847314 : Nat := 4983230072969 + 3 ^ 40 * 2847314 * 2
def baseEnd_2847314 : Nat := 487346885425326034860149

theorem tailTrace_2847314 : CollatzResearch.WordTrace tailWord_2847314 prefixEnd_2847314 487346885425326034860149 := by
  unfold tailWord_2847314
  simp only [CollatzResearch.WordTrace]
  refine ⟨25962518301668783840345249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69233382137783423574253997 25962518301668783840345249)
  ·
    refine ⟨19471888726251587880258937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25962518301668783840345249 19471888726251587880258937)
    ·
      refine ⟨14603916544688690910194203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19471888726251587880258937 14603916544688690910194203)
      ·
        refine ⟨21905874817033036365291305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14603916544688690910194203 21905874817033036365291305)
        ·
          refine ⟨16429406112774777273968479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21905874817033036365291305 16429406112774777273968479)
          ·
            refine ⟨24644109169162165910952719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16429406112774777273968479 24644109169162165910952719)
            ·
              refine ⟨36966163753743248866429079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24644109169162165910952719 36966163753743248866429079)
              ·
                refine ⟨55449245630614873299643619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36966163753743248866429079 55449245630614873299643619)
                ·
                  refine ⟨83173868445922309949465429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 55449245630614873299643619 83173868445922309949465429)
                  ·
                    refine ⟨487346885425326034860149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 83173868445922309949465429 487346885425326034860149)
                    ·
                      rfl

theorem cell23_2847314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 1, 1, 9].length) (baseStart_2847314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2847314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2847314 prefixEnd_2847314 := by exact prefixLift 2847314
  have htrace : WordTrace (prefixWord ++ tailWord_2847314) baseStart_2847314 baseEnd_2847314 := by
    simpa [prefixWord, tailWord_2847314, baseEnd_2847314] using wordTrace_append hprefix tailTrace_2847314
  have hstable : (prefixWord ++ tailWord_2847314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2847314).length < 2 ^ (prefixWord ++ tailWord_2847314).sum := by decide
  have hdescent : baseEnd_2847314 < baseStart_2847314 := by decide
  rcases family_descends (prefixWord ++ tailWord_2847314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2847328 : List Nat := [2, 1, 1, 3, 2, 1, 4, 3, 2, 1, 3]
def baseStart_2847328 : Nat := 118140960795 + 2847328 * 2 ^ 59
def prefixEnd_2847328 : Nat := 4983230072969 + 3 ^ 40 * 2847328 * 2
def baseEnd_2847328 : Nat := 1462047845005141049805383

theorem tailTrace_2847328 : CollatzResearch.WordTrace tailWord_2847328 prefixEnd_2847328 1462047845005141049805383 := by
  unfold tailWord_2847328
  simp only [CollatzResearch.WordTrace]
  refine ⟨51925291914312207876195319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69233722552416277168260425 51925291914312207876195319)
  ·
    refine ⟨77887937871468311814292979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51925291914312207876195319 77887937871468311814292979)
    ·
      refine ⟨116831906807202467721439469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77887937871468311814292979 116831906807202467721439469)
      ·
        refine ⟨43811965052700925395539801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 116831906807202467721439469 43811965052700925395539801)
        ·
          refine ⟨32858973789525694046654851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43811965052700925395539801 32858973789525694046654851)
          ·
            refine ⟨49288460684288541069982277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32858973789525694046654851 49288460684288541069982277)
            ·
              refine ⟨9241586378304101450621677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 49288460684288541069982277 9241586378304101450621677)
              ·
                refine ⟨3465594891864038043983129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9241586378304101450621677 3465594891864038043983129)
                ·
                  refine ⟨2599196168898028532987347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3465594891864038043983129 2599196168898028532987347)
                  ·
                    refine ⟨3898794253347042799481021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2599196168898028532987347 3898794253347042799481021)
                    ·
                      refine ⟨1462047845005141049805383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3898794253347042799481021 1462047845005141049805383)
                      ·
                        rfl

theorem cell23_2847328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 4, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 4, 3, 2, 1, 3].length) (baseStart_2847328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2847328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2847328 prefixEnd_2847328 := by exact prefixLift 2847328
  have htrace : WordTrace (prefixWord ++ tailWord_2847328) baseStart_2847328 baseEnd_2847328 := by
    simpa [prefixWord, tailWord_2847328, baseEnd_2847328] using wordTrace_append hprefix tailTrace_2847328
  have hstable : (prefixWord ++ tailWord_2847328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2847328).length < 2 ^ (prefixWord ++ tailWord_2847328).sum := by decide
  have hdescent : baseEnd_2847328 < baseStart_2847328 := by decide
  rcases family_descends (prefixWord ++ tailWord_2847328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2847338 : List Nat := [3, 1, 3, 2, 1, 1, 1, 3, 3, 3, 2]
def baseStart_2847338 : Nat := 118140960795 + 2847338 * 2 ^ 59
def prefixEnd_2847338 : Nat := 4983230072969 + 3 ^ 40 * 2847338 * 2
def baseEnd_2847338 : Nat := 1462052979811686010680337

theorem tailTrace_2847338 : CollatzResearch.WordTrace tailWord_2847338 prefixEnd_2847338 1462052979811686010680337 := by
  unfold tailWord_2847338
  simp only [CollatzResearch.WordTrace]
  refine ⟨25962737139647046865063667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69233965705725458306836445 25962737139647046865063667)
  ·
    refine ⟨38944105709470570297595501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25962737139647046865063667 38944105709470570297595501)
    ·
      refine ⟨14604039641051463861598313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38944105709470570297595501 14604039641051463861598313)
      ·
        refine ⟨10953029730788597896198735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14604039641051463861598313 10953029730788597896198735)
        ·
          refine ⟨16429544596182896844298103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10953029730788597896198735 16429544596182896844298103)
          ·
            refine ⟨24644316894274345266447155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16429544596182896844298103 24644316894274345266447155)
            ·
              refine ⟨36966475341411517899670733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24644316894274345266447155 36966475341411517899670733)
              ·
                refine ⟨13862428253029319212376525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36966475341411517899670733 13862428253029319212376525)
                ·
                  refine ⟨5198410594885994704641197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13862428253029319212376525 5198410594885994704641197)
                  ·
                    refine ⟨1949403973082248014240449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5198410594885994704641197 1949403973082248014240449)
                    ·
                      refine ⟨1462052979811686010680337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1949403973082248014240449 1462052979811686010680337)
                      ·
                        rfl

theorem cell23_2847338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 3, 3, 3, 2].length) (baseStart_2847338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2847338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2847338 prefixEnd_2847338 := by exact prefixLift 2847338
  have htrace : WordTrace (prefixWord ++ tailWord_2847338) baseStart_2847338 baseEnd_2847338 := by
    simpa [prefixWord, tailWord_2847338, baseEnd_2847338] using wordTrace_append hprefix tailTrace_2847338
  have hstable : (prefixWord ++ tailWord_2847338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2847338).length < 2 ^ (prefixWord ++ tailWord_2847338).sum := by decide
  have hdescent : baseEnd_2847338 < baseStart_2847338 := by decide
  rcases family_descends (prefixWord ++ tailWord_2847338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2847349 : List Nat := [1, 3, 4, 2, 3, 1, 2, 1, 1, 2, 3]
def baseStart_2847349 : Nat := 118140960795 + 2847349 * 2 ^ 59
def prefixEnd_2847349 : Nat := 4983230072969 + 3 ^ 40 * 2847349 * 2
def baseEnd_2847349 : Nat := 1462058628098885467642787

theorem tailTrace_2847349 : CollatzResearch.WordTrace tailWord_2847349 prefixEnd_2847349 1462058628098885467642787 := by
  unfold tailWord_2847349
  simp only [CollatzResearch.WordTrace]
  refine ⟨103851349761548336338905101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69234233174365557559270067 103851349761548336338905101)
  ·
    refine ⟨38944256160580626127089413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 103851349761548336338905101 38944256160580626127089413)
    ·
      refine ⟨7302048030108867398829265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 38944256160580626127089413 7302048030108867398829265)
      ·
        refine ⟨5476536022581650549121949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7302048030108867398829265 5476536022581650549121949)
        ·
          refine ⟨2053701008468118955920731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5476536022581650549121949 2053701008468118955920731)
          ·
            refine ⟨3080551512702178433881097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2053701008468118955920731 3080551512702178433881097)
            ·
              refine ⟨2310413634526633825410823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3080551512702178433881097 2310413634526633825410823)
              ·
                refine ⟨3465620451789950738116235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2310413634526633825410823 3465620451789950738116235)
                ·
                  refine ⟨5198430677684926107174353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3465620451789950738116235 5198430677684926107174353)
                  ·
                    refine ⟨3898823008263694580380765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5198430677684926107174353 3898823008263694580380765)
                    ·
                      refine ⟨1462058628098885467642787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3898823008263694580380765 1462058628098885467642787)
                      ·
                        rfl

theorem cell23_2847349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 3, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 3, 1, 2, 1, 1, 2, 3].length) (baseStart_2847349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2847349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2847349 prefixEnd_2847349 := by exact prefixLift 2847349
  have htrace : WordTrace (prefixWord ++ tailWord_2847349) baseStart_2847349 baseEnd_2847349 := by
    simpa [prefixWord, tailWord_2847349, baseEnd_2847349] using wordTrace_append hprefix tailTrace_2847349
  have hstable : (prefixWord ++ tailWord_2847349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2847349).length < 2 ^ (prefixWord ++ tailWord_2847349).sum := by decide
  have hdescent : baseEnd_2847349 < baseStart_2847349 := by decide
  rcases family_descends (prefixWord ++ tailWord_2847349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2847354 : List Nat := [3, 1, 1, 1, 1, 1, 1, 2, 6, 1, 5]
def baseStart_2847354 : Nat := 118140960795 + 2847354 * 2 ^ 59
def prefixEnd_2847354 : Nat := 4983230072969 + 3 ^ 40 * 2847354 * 2
def baseEnd_2847354 : Nat := 1462061195502157948080263

theorem tailTrace_2847354 : CollatzResearch.WordTrace tailWord_2847354 prefixEnd_2847354 1462061195502157948080263 := by
  unfold tailWord_2847354
  simp only [CollatzResearch.WordTrace]
  refine ⟨25962883031632555548209279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69234354751020148128558077 25962883031632555548209279)
  ·
    refine ⟨38944324547448833322313919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25962883031632555548209279 38944324547448833322313919)
    ·
      refine ⟨58416486821173249983470879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38944324547448833322313919 58416486821173249983470879)
      ·
        refine ⟨87624730231759874975206319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58416486821173249983470879 87624730231759874975206319)
        ·
          refine ⟨131437095347639812462809479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87624730231759874975206319 131437095347639812462809479)
          ·
            refine ⟨197155643021459718694214219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 131437095347639812462809479 197155643021459718694214219)
            ·
              refine ⟨295733464532189578041321329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 197155643021459718694214219 295733464532189578041321329)
              ·
                refine ⟨221800098399142183530990997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 295733464532189578041321329 221800098399142183530990997)
                ·
                  refine ⟨10396879612459789853015203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 221800098399142183530990997 10396879612459789853015203)
                  ·
                    refine ⟨15595319418689684779522805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10396879612459789853015203 15595319418689684779522805)
                    ·
                      refine ⟨1462061195502157948080263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15595319418689684779522805 1462061195502157948080263)
                      ·
                        rfl

theorem cell23_2847354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 2, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 2, 6, 1, 5].length) (baseStart_2847354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2847354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2847354 prefixEnd_2847354 := by exact prefixLift 2847354
  have htrace : WordTrace (prefixWord ++ tailWord_2847354) baseStart_2847354 baseEnd_2847354 := by
    simpa [prefixWord, tailWord_2847354, baseEnd_2847354] using wordTrace_append hprefix tailTrace_2847354
  have hstable : (prefixWord ++ tailWord_2847354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2847354).length < 2 ^ (prefixWord ++ tailWord_2847354).sum := by decide
  have hdescent : baseEnd_2847354 < baseStart_2847354 := by decide
  rcases family_descends (prefixWord ++ tailWord_2847354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2847421 : List Nat := [1, 4, 1, 2, 1, 3, 1, 1, 4, 5]
def baseStart_2847421 : Nat := 118140960795 + 2847421 * 2 ^ 59
def prefixEnd_2847421 : Nat := 4983230072969 + 3 ^ 40 * 2847421 * 2
def baseEnd_2847421 : Nat := 487365199568669728647485

theorem tailTrace_2847421 : CollatzResearch.WordTrace tailWord_2847421 prefixEnd_2847421 487365199568669728647485 := by
  unfold tailWord_2847421
  simp only [CollatzResearch.WordTrace]
  refine ⟨103853975817287492635526117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69235983878191661757017411 103853975817287492635526117)
  ·
    refine ⟨19472620465741404869161147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 103853975817287492635526117 19472620465741404869161147)
    ·
      refine ⟨29208930698612107303741721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19472620465741404869161147 29208930698612107303741721)
      ·
        refine ⟨21906698023959080477806291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29208930698612107303741721 21906698023959080477806291)
        ·
          refine ⟨32860047035938620716709437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21906698023959080477806291 32860047035938620716709437)
          ·
            refine ⟨12322517638476982768766039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32860047035938620716709437 12322517638476982768766039)
            ·
              refine ⟨18483776457715474153149059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12322517638476982768766039 18483776457715474153149059)
              ·
                refine ⟨27725664686573211229723589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18483776457715474153149059 27725664686573211229723589)
                ·
                  refine ⟨5198562128732477105573173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27725664686573211229723589 5198562128732477105573173)
                  ·
                    refine ⟨487365199568669728647485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5198562128732477105573173 487365199568669728647485)
                    ·
                      rfl

theorem cell23_2847421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 1, 1, 4, 5].length) (baseStart_2847421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2847421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2847421 prefixEnd_2847421 := by exact prefixLift 2847421
  have htrace : WordTrace (prefixWord ++ tailWord_2847421) baseStart_2847421 baseEnd_2847421 := by
    simpa [prefixWord, tailWord_2847421, baseEnd_2847421] using wordTrace_append hprefix tailTrace_2847421
  have hstable : (prefixWord ++ tailWord_2847421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2847421).length < 2 ^ (prefixWord ++ tailWord_2847421).sum := by decide
  have hdescent : baseEnd_2847421 < baseStart_2847421 := by decide
  rcases family_descends (prefixWord ++ tailWord_2847421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2847441 : List Nat := [1, 2, 2, 1, 2, 3, 1, 2, 4, 1, 4]
def baseStart_2847441 : Nat := 118140960795 + 2847441 * 2 ^ 59
def prefixEnd_2847441 : Nat := 4983230072969 + 3 ^ 40 * 2847441 * 2
def baseEnd_2847441 : Nat := 1462105868319099107692363

theorem tailTrace_2847441 : CollatzResearch.WordTrace tailWord_2847441 prefixEnd_2847441 1462105868319099107692363 := by
  unfold tailWord_2847441
  simp only [CollatzResearch.WordTrace]
  refine ⟨103854705277215036051254177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69236470184810024034169451 103854705277215036051254177)
  ·
    refine ⟨77891028957911277038440633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103854705277215036051254177 77891028957911277038440633)
    ·
      refine ⟨58418271718433457778830475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77891028957911277038440633 58418271718433457778830475)
      ·
        refine ⟨87627407577650186668245713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58418271718433457778830475 87627407577650186668245713)
        ·
          refine ⟨65720555683237640001184285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87627407577650186668245713 65720555683237640001184285)
          ·
            refine ⟨24645208381214115000444107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 65720555683237640001184285 24645208381214115000444107)
            ·
              refine ⟨36967812571821172500666161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24645208381214115000444107 36967812571821172500666161)
              ·
                refine ⟨27725859428865879375499621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36967812571821172500666161 27725859428865879375499621)
                ·
                  refine ⟨5198598642912352382906179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27725859428865879375499621 5198598642912352382906179)
                  ·
                    refine ⟨7797897964368528574359269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5198598642912352382906179 7797897964368528574359269)
                    ·
                      refine ⟨1462105868319099107692363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7797897964368528574359269 1462105868319099107692363)
                      ·
                        rfl

theorem cell23_2847441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 2, 4, 1, 4].length) (baseStart_2847441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2847441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2847441 prefixEnd_2847441 := by exact prefixLift 2847441
  have htrace : WordTrace (prefixWord ++ tailWord_2847441) baseStart_2847441 baseEnd_2847441 := by
    simpa [prefixWord, tailWord_2847441, baseEnd_2847441] using wordTrace_append hprefix tailTrace_2847441
  have hstable : (prefixWord ++ tailWord_2847441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2847441).length < 2 ^ (prefixWord ++ tailWord_2847441).sum := by decide
  have hdescent : baseEnd_2847441 < baseStart_2847441 := by decide
  rcases family_descends (prefixWord ++ tailWord_2847441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2847476 : List Nat := [2, 6, 1, 1, 2, 2, 2, 2, 5]
def baseStart_2847476 : Nat := 118140960795 + 2847476 * 2 ^ 59
def prefixEnd_2847476 : Nat := 4983230072969 + 3 ^ 40 * 2847476 * 2
def baseEnd_2847476 : Nat := 162458204460222941194967

theorem tailTrace_2847476 : CollatzResearch.WordTrace tailWord_2847476 prefixEnd_2847476 162458204460222941194967 := by
  unfold tailWord_2847476
  simp only [CollatzResearch.WordTrace]
  refine ⟨51927990916044118514389141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69237321221392158019185521 51927990916044118514389141)
  ·
    refine ⟨2434124574189568055361991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 51927990916044118514389141 2434124574189568055361991)
    ·
      refine ⟨3651186861284352083042987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2434124574189568055361991 3651186861284352083042987)
      ·
        refine ⟨5476780291926528124564481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3651186861284352083042987 5476780291926528124564481)
        ·
          refine ⟨4107585218944896093423361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5476780291926528124564481 4107585218944896093423361)
          ·
            refine ⟨3080688914208672070067521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4107585218944896093423361 3080688914208672070067521)
            ·
              refine ⟨2310516685656504052550641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3080688914208672070067521 2310516685656504052550641)
              ·
                refine ⟨1732887514242378039412981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2310516685656504052550641 1732887514242378039412981)
                ·
                  refine ⟨162458204460222941194967, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1732887514242378039412981 162458204460222941194967)
                  ·
                    rfl

theorem cell23_2847476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 2, 2, 2, 5].length) (baseStart_2847476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2847476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2847476 prefixEnd_2847476 := by exact prefixLift 2847476
  have htrace : WordTrace (prefixWord ++ tailWord_2847476) baseStart_2847476 baseEnd_2847476 := by
    simpa [prefixWord, tailWord_2847476, baseEnd_2847476] using wordTrace_append hprefix tailTrace_2847476
  have hstable : (prefixWord ++ tailWord_2847476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2847476).length < 2 ^ (prefixWord ++ tailWord_2847476).sum := by decide
  have hdescent : baseEnd_2847476 < baseStart_2847476 := by decide
  rcases family_descends (prefixWord ++ tailWord_2847476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2847485 : List Nat := [1, 4, 1, 1, 1, 1, 5, 4, 1, 4]
def baseStart_2847485 : Nat := 118140960795 + 2847485 * 2 ^ 59
def prefixEnd_2847485 : Nat := 4983230072969 + 3 ^ 40 * 2847485 * 2
def baseEnd_2847485 : Nat := 487376153822632311847387

theorem tailTrace_2847485 : CollatzResearch.WordTrace tailWord_2847485 prefixEnd_2847485 487376153822632311847387 := by
  unfold tailWord_2847485
  simp only [CollatzResearch.WordTrace]
  refine ⟨103856310089055631565855909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69237540059370421043903939 103856310089055631565855909)
  ·
    refine ⟨19473058141697930918597983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 103856310089055631565855909 19473058141697930918597983)
    ·
      refine ⟨29209587212546896377896975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19473058141697930918597983 29209587212546896377896975)
      ·
        refine ⟨43814380818820344566845463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29209587212546896377896975 43814380818820344566845463)
        ·
          refine ⟨65721571228230516850268195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43814380818820344566845463 65721571228230516850268195)
          ·
            refine ⟨98582356842345775275402293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65721571228230516850268195 98582356842345775275402293)
            ·
              refine ⟨9242095953969916432068965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 98582356842345775275402293 9242095953969916432068965)
              ·
                refine ⟨1732892991369359331012931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9242095953969916432068965 1732892991369359331012931)
                ·
                  refine ⟨2599339487054038996519397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1732892991369359331012931 2599339487054038996519397)
                  ·
                    refine ⟨487376153822632311847387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2599339487054038996519397 487376153822632311847387)
                    ·
                      rfl

theorem cell23_2847485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 5, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 5, 4, 1, 4].length) (baseStart_2847485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2847485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2847485 prefixEnd_2847485 := by exact prefixLift 2847485
  have htrace : WordTrace (prefixWord ++ tailWord_2847485) baseStart_2847485 baseEnd_2847485 := by
    simpa [prefixWord, tailWord_2847485, baseEnd_2847485] using wordTrace_append hprefix tailTrace_2847485
  have hstable : (prefixWord ++ tailWord_2847485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2847485).length < 2 ^ (prefixWord ++ tailWord_2847485).sum := by decide
  have hdescent : baseEnd_2847485 < baseStart_2847485 := by decide
  rcases family_descends (prefixWord ++ tailWord_2847485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2847491 : List Nat := [1, 1, 1, 3, 2, 2, 1, 2, 2, 5, 3]
def baseStart_2847491 : Nat := 118140960795 + 2847491 * 2 ^ 59
def prefixEnd_2847491 : Nat := 4983230072969 + 3 ^ 40 * 2847491 * 2
def baseEnd_2847491 : Nat := 1462131542351823912067133

theorem tailTrace_2847491 : CollatzResearch.WordTrace tailWord_2847491 prefixEnd_2847491 1462131542351823912067133 := by
  unfold tailWord_2847491
  simp only [CollatzResearch.WordTrace]
  refine ⟨103856528927033894590574327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69237685951355929727049551 103856528927033894590574327)
  ·
    refine ⟨155784793390550841885861491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103856528927033894590574327 155784793390550841885861491)
    ·
      refine ⟨233677190085826262828792237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155784793390550841885861491 233677190085826262828792237)
      ·
        refine ⟨87628946282184848560797089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 233677190085826262828792237 87628946282184848560797089)
        ·
          refine ⟨65721709711638636420597817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87628946282184848560797089 65721709711638636420597817)
          ·
            refine ⟨49291282283728977315448363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65721709711638636420597817 49291282283728977315448363)
            ·
              refine ⟨73936923425593465973172545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49291282283728977315448363 73936923425593465973172545)
              ·
                refine ⟨55452692569195099479879409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 73936923425593465973172545 55452692569195099479879409)
                ·
                  refine ⟨41589519426896324609909557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 55452692569195099479879409 41589519426896324609909557)
                  ·
                    refine ⟨3899017446271530432179021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 41589519426896324609909557 3899017446271530432179021)
                    ·
                      refine ⟨1462131542351823912067133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3899017446271530432179021 1462131542351823912067133)
                      ·
                        rfl

theorem cell23_2847491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 2, 2, 5, 3].length) (baseStart_2847491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2847491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2847491 prefixEnd_2847491 := by exact prefixLift 2847491
  have htrace : WordTrace (prefixWord ++ tailWord_2847491) baseStart_2847491 baseEnd_2847491 := by
    simpa [prefixWord, tailWord_2847491, baseEnd_2847491] using wordTrace_append hprefix tailTrace_2847491
  have hstable : (prefixWord ++ tailWord_2847491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2847491).length < 2 ^ (prefixWord ++ tailWord_2847491).sum := by decide
  have hdescent : baseEnd_2847491 < baseStart_2847491 := by decide
  rcases family_descends (prefixWord ++ tailWord_2847491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2847568 : List Nat := [2, 1, 1, 1, 1, 4, 2, 3, 3, 2, 3]
def baseStart_2847568 : Nat := 118140960795 + 2847568 * 2 ^ 59
def prefixEnd_2847568 : Nat := 4983230072969 + 3 ^ 40 * 2847568 * 2
def baseEnd_2847568 : Nat := 1462171080362220110804279

theorem tailTrace_2847568 : CollatzResearch.WordTrace tailWord_2847568 prefixEnd_2847568 1462171080362220110804279 := by
  unfold tailWord_2847568
  simp only [CollatzResearch.WordTrace]
  refine ⟨51929668673877468370563679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69239558231836624494084905 51929668673877468370563679)
  ·
    refine ⟨77894503010816202555845519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51929668673877468370563679 77894503010816202555845519)
    ·
      refine ⟨116841754516224303833768279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77894503010816202555845519 116841754516224303833768279)
      ·
        refine ⟨175262631774336455750652419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116841754516224303833768279 175262631774336455750652419)
        ·
          refine ⟨262893947661504683625978629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 175262631774336455750652419 262893947661504683625978629)
          ·
            refine ⟨49292615186532128179870993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 262893947661504683625978629 49292615186532128179870993)
            ·
              refine ⟨36969461389899096134903245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49292615186532128179870993 36969461389899096134903245)
              ·
                refine ⟨13863548021212161050588717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36969461389899096134903245 13863548021212161050588717)
                ·
                  refine ⟨5198830507954560393970769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13863548021212161050588717 5198830507954560393970769)
                  ·
                    refine ⟨3899122880965920295478077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5198830507954560393970769 3899122880965920295478077)
                    ·
                      refine ⟨1462171080362220110804279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3899122880965920295478077 1462171080362220110804279)
                      ·
                        rfl

theorem cell23_2847568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 3, 3, 2, 3].length) (baseStart_2847568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2847568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2847568 prefixEnd_2847568 := by exact prefixLift 2847568
  have htrace : WordTrace (prefixWord ++ tailWord_2847568) baseStart_2847568 baseEnd_2847568 := by
    simpa [prefixWord, tailWord_2847568, baseEnd_2847568] using wordTrace_append hprefix tailTrace_2847568
  have hstable : (prefixWord ++ tailWord_2847568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2847568).length < 2 ^ (prefixWord ++ tailWord_2847568).sum := by decide
  have hdescent : baseEnd_2847568 < baseStart_2847568 := by decide
  rcases family_descends (prefixWord ++ tailWord_2847568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2847588 : List Nat := [2, 3, 1, 1, 4, 3, 9]
def baseStart_2847588 : Nat := 118140960795 + 2847588 * 2 ^ 59
def prefixEnd_2847588 : Nat := 4983230072969 + 3 ^ 40 * 2847588 * 2
def baseEnd_2847588 : Nat := 18051621604633457192027

theorem tailTrace_2847588 : CollatzResearch.WordTrace tailWord_2847588 prefixEnd_2847588 18051621604633457192027 := by
  unfold tailWord_2847588
  simp only [CollatzResearch.WordTrace]
  refine ⟨51930033403841240078427709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69240044538454986771236945 51930033403841240078427709)
  ·
    refine ⟨19473762526440465029410391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51930033403841240078427709 19473762526440465029410391)
    ·
      refine ⟨29210643789660697544115587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19473762526440465029410391 29210643789660697544115587)
      ·
        refine ⟨43815965684491046316173381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29210643789660697544115587 43815965684491046316173381)
        ·
          refine ⟨8215493565842071184282509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 43815965684491046316173381 8215493565842071184282509)
          ·
            refine ⟨3080810087190776694105941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8215493565842071184282509 3080810087190776694105941)
            ·
              refine ⟨18051621604633457192027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3080810087190776694105941 18051621604633457192027)
              ·
                rfl

theorem cell23_2847588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 3, 9].length) (baseStart_2847588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2847588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2847588 prefixEnd_2847588 := by exact prefixLift 2847588
  have htrace : WordTrace (prefixWord ++ tailWord_2847588) baseStart_2847588 baseEnd_2847588 := by
    simpa [prefixWord, tailWord_2847588, baseEnd_2847588] using wordTrace_append hprefix tailTrace_2847588
  have hstable : (prefixWord ++ tailWord_2847588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2847588).length < 2 ^ (prefixWord ++ tailWord_2847588).sum := by decide
  have hdescent : baseEnd_2847588 < baseStart_2847588 := by decide
  rcases family_descends (prefixWord ++ tailWord_2847588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2847649 : List Nat := [1, 2, 3, 4, 1, 2, 2, 2, 2, 1, 3]
def baseStart_2847649 : Nat := 118140960795 + 2847649 * 2 ^ 59
def prefixEnd_2847649 : Nat := 4983230072969 + 3 ^ 40 * 2847649 * 2
def baseEnd_2847649 : Nat := 1462212672295234293891407

theorem tailTrace_2847649 : CollatzResearch.WordTrace tailWord_2847649 prefixEnd_2847649 1462212672295234293891407 := by
  unfold tailWord_2847649
  simp only [CollatzResearch.WordTrace]
  refine ⟨103862291660461487574826001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69241527773640991716550667 103862291660461487574826001)
  ·
    refine ⟨77896718745346115681119501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103862291660461487574826001 77896718745346115681119501)
    ·
      refine ⟨29211269529504793380419813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 77896718745346115681119501 29211269529504793380419813)
      ·
        refine ⟨5477113036782148758828715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29211269529504793380419813 5477113036782148758828715)
        ·
          refine ⟨8215669555173223138243073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5477113036782148758828715 8215669555173223138243073)
          ·
            refine ⟨6161752166379917353682305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8215669555173223138243073 6161752166379917353682305)
            ·
              refine ⟨4621314124784938015261729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6161752166379917353682305 4621314124784938015261729)
              ·
                refine ⟨3465985593588703511446297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4621314124784938015261729 3465985593588703511446297)
                ·
                  refine ⟨2599489195191527633584723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3465985593588703511446297 2599489195191527633584723)
                  ·
                    refine ⟨3899233792787291450377085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2599489195191527633584723 3899233792787291450377085)
                    ·
                      refine ⟨1462212672295234293891407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3899233792787291450377085 1462212672295234293891407)
                      ·
                        rfl

theorem cell23_2847649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 2, 2, 2, 1, 3].length) (baseStart_2847649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2847649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2847649 prefixEnd_2847649 := by exact prefixLift 2847649
  have htrace : WordTrace (prefixWord ++ tailWord_2847649) baseStart_2847649 baseEnd_2847649 := by
    simpa [prefixWord, tailWord_2847649, baseEnd_2847649] using wordTrace_append hprefix tailTrace_2847649
  have hstable : (prefixWord ++ tailWord_2847649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2847649).length < 2 ^ (prefixWord ++ tailWord_2847649).sum := by decide
  have hdescent : baseEnd_2847649 < baseStart_2847649 := by decide
  rcases family_descends (prefixWord ++ tailWord_2847649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2847665 : List Nat := [1, 2, 2, 4, 3, 1, 1, 1, 2, 6]
def baseStart_2847665 : Nat := 118140960795 + 2847665 * 2 ^ 59
def prefixEnd_2847665 : Nat := 4983230072969 + 3 ^ 40 * 2847665 * 2
def baseEnd_2847665 : Nat := 487406962661902077097111

theorem tailTrace_2847665 : CollatzResearch.WordTrace tailWord_2847665 prefixEnd_2847665 487406962661902077097111 := by
  unfold tailWord_2847665
  simp only [CollatzResearch.WordTrace]
  refine ⟨103862875228403522307408449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69241916818935681538272299 103862875228403522307408449)
  ·
    refine ⟨77897156421302641730556337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103862875228403522307408449 77897156421302641730556337)
    ·
      refine ⟨58422867315976981297917253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77897156421302641730556337 58422867315976981297917253)
      ·
        refine ⟨10954287621745683993359485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 58422867315976981297917253 10954287621745683993359485)
        ·
          refine ⟨4107857858154631497509807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10954287621745683993359485 4107857858154631497509807)
          ·
            refine ⟨6161786787231947246264711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4107857858154631497509807 6161786787231947246264711)
            ·
              refine ⟨9242680180847920869397067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6161786787231947246264711 9242680180847920869397067)
              ·
                refine ⟨13864020271271881304095601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9242680180847920869397067 13864020271271881304095601)
                ·
                  refine ⟨10398015203453910978071701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13864020271271881304095601 10398015203453910978071701)
                  ·
                    refine ⟨487406962661902077097111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10398015203453910978071701 487406962661902077097111)
                    ·
                      rfl

theorem cell23_2847665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 1, 1, 2, 6].length) (baseStart_2847665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2847665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2847665 prefixEnd_2847665 := by exact prefixLift 2847665
  have htrace : WordTrace (prefixWord ++ tailWord_2847665) baseStart_2847665 baseEnd_2847665 := by
    simpa [prefixWord, tailWord_2847665, baseEnd_2847665] using wordTrace_append hprefix tailTrace_2847665
  have hstable : (prefixWord ++ tailWord_2847665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2847665).length < 2 ^ (prefixWord ++ tailWord_2847665).sum := by decide
  have hdescent : baseEnd_2847665 < baseStart_2847665 := by decide
  rcases family_descends (prefixWord ++ tailWord_2847665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2847672 : List Nat := [2, 1, 2, 1, 2, 5, 2, 1, 1, 4, 2]
def baseStart_2847672 : Nat := 118140960795 + 2847672 * 2 ^ 59
def prefixEnd_2847672 : Nat := 4983230072969 + 3 ^ 40 * 2847672 * 2
def baseEnd_2847672 : Nat := 1462224482350287703903801

theorem tailTrace_2847672 : CollatzResearch.WordTrace tailWord_2847672 prefixEnd_2847672 1462224482350287703903801 := by
  unfold tailWord_2847672
  simp only [CollatzResearch.WordTrace]
  refine ⟨51931565269689081251456635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69242087026252108335275513 51931565269689081251456635)
  ·
    refine ⟨77897347904533621877184953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51931565269689081251456635 77897347904533621877184953)
    ·
      refine ⟨58423010928400216407888715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77897347904533621877184953 58423010928400216407888715)
      ·
        refine ⟨87634516392600324611833073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58423010928400216407888715 87634516392600324611833073)
        ·
          refine ⟨65725887294450243458874805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87634516392600324611833073 65725887294450243458874805)
          ·
            refine ⟨6161801933854710324269513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 65725887294450243458874805 6161801933854710324269513)
            ·
              refine ⟨4621351450391032743202135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6161801933854710324269513 4621351450391032743202135)
              ·
                refine ⟨6932027175586549114803203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4621351450391032743202135 6932027175586549114803203)
                ·
                  refine ⟨10398040763379823672204805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6932027175586549114803203 10398040763379823672204805)
                  ·
                    refine ⟨1949632643133716938538401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10398040763379823672204805 1949632643133716938538401)
                    ·
                      refine ⟨1462224482350287703903801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1949632643133716938538401 1462224482350287703903801)
                      ·
                        rfl

theorem cell23_2847672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 2, 1, 1, 4, 2].length) (baseStart_2847672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2847672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2847672 prefixEnd_2847672 := by exact prefixLift 2847672
  have htrace : WordTrace (prefixWord ++ tailWord_2847672) baseStart_2847672 baseEnd_2847672 := by
    simpa [prefixWord, tailWord_2847672, baseEnd_2847672] using wordTrace_append hprefix tailTrace_2847672
  have hstable : (prefixWord ++ tailWord_2847672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2847672).length < 2 ^ (prefixWord ++ tailWord_2847672).sum := by decide
  have hdescent : baseEnd_2847672 < baseStart_2847672 := by decide
  rcases family_descends (prefixWord ++ tailWord_2847672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2847695 : List Nat := [1, 1, 2, 1, 1, 6, 1, 5, 5]
def baseStart_2847695 : Nat := 118140960795 + 2847695 * 2 ^ 59
def prefixEnd_2847695 : Nat := 4983230072969 + 3 ^ 40 * 2847695 * 2
def baseEnd_2847695 : Nat := 162470699156149012657355

theorem tailTrace_2847695 : CollatzResearch.WordTrace tailWord_2847695 prefixEnd_2847695 162470699156149012657355 := by
  unfold tailWord_2847695
  simp only [CollatzResearch.WordTrace]
  refine ⟨103863969418294837431000539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69242646278863224954000359 103863969418294837431000539)
  ·
    refine ⟨155795954127442256146500809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103863969418294837431000539 155795954127442256146500809)
    ·
      refine ⟨116846965595581692109875607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 155795954127442256146500809 116846965595581692109875607)
      ·
        refine ⟨175270448393372538164813411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116846965595581692109875607 175270448393372538164813411)
        ·
          refine ⟨262905672590058807247220117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 175270448393372538164813411 262905672590058807247220117)
          ·
            refine ⟨12323703402659006589713443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 262905672590058807247220117 12323703402659006589713443)
            ·
              refine ⟨18485555103988509884570165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12323703402659006589713443 18485555103988509884570165)
              ·
                refine ⟨1733020790998922801678453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 18485555103988509884570165 1733020790998922801678453)
                ·
                  refine ⟨162470699156149012657355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1733020790998922801678453 162470699156149012657355)
                  ·
                    rfl

theorem cell23_2847695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 1, 5, 5].length) (baseStart_2847695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2847695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2847695 prefixEnd_2847695 := by exact prefixLift 2847695
  have htrace : WordTrace (prefixWord ++ tailWord_2847695) baseStart_2847695 baseEnd_2847695 := by
    simpa [prefixWord, tailWord_2847695, baseEnd_2847695] using wordTrace_append hprefix tailTrace_2847695
  have hstable : (prefixWord ++ tailWord_2847695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2847695).length < 2 ^ (prefixWord ++ tailWord_2847695).sum := by decide
  have hdescent : baseEnd_2847695 < baseStart_2847695 := by decide
  rcases family_descends (prefixWord ++ tailWord_2847695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2847702 : List Nat := [5, 2, 1, 1, 2, 1, 1, 2, 2, 2, 4]
def baseStart_2847702 : Nat := 118140960795 + 2847702 * 2 ^ 59
def prefixEnd_2847702 : Nat := 4983230072969 + 3 ^ 40 * 2847702 * 2
def baseEnd_2847702 : Nat := 1462239886769922586528663

theorem tailTrace_2847702 : CollatzResearch.WordTrace tailWord_2847702 prefixEnd_2847702 1462239886769922586528663 := by
  unfold tailWord_2847702
  simp only [CollatzResearch.WordTrace]
  refine ⟨6491514045579342351656585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 69242816486179651751003573 6491514045579342351656585)
  ·
    refine ⟨4868635534184506763742439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6491514045579342351656585 4868635534184506763742439)
    ·
      refine ⟨7302953301276760145613659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4868635534184506763742439 7302953301276760145613659)
      ·
        refine ⟨10954429951915140218420489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7302953301276760145613659 10954429951915140218420489)
        ·
          refine ⟨8215822463936355163815367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10954429951915140218420489 8215822463936355163815367)
          ·
            refine ⟨12323733695904532745723051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8215822463936355163815367 12323733695904532745723051)
            ·
              refine ⟨18485600543856799118584577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12323733695904532745723051 18485600543856799118584577)
              ·
                refine ⟨13864200407892599338938433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18485600543856799118584577 13864200407892599338938433)
                ·
                  refine ⟨10398150305919449504203825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13864200407892599338938433 10398150305919449504203825)
                  ·
                    refine ⟨7798612729439587128152869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10398150305919449504203825 7798612729439587128152869)
                    ·
                      refine ⟨1462239886769922586528663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7798612729439587128152869 1462239886769922586528663)
                      ·
                        rfl

theorem cell23_2847702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 1, 2, 2, 2, 4].length) (baseStart_2847702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2847702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2847702 prefixEnd_2847702 := by exact prefixLift 2847702
  have htrace : WordTrace (prefixWord ++ tailWord_2847702) baseStart_2847702 baseEnd_2847702 := by
    simpa [prefixWord, tailWord_2847702, baseEnd_2847702] using wordTrace_append hprefix tailTrace_2847702
  have hstable : (prefixWord ++ tailWord_2847702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2847702).length < 2 ^ (prefixWord ++ tailWord_2847702).sum := by decide
  have hdescent : baseEnd_2847702 < baseStart_2847702 := by decide
  rcases family_descends (prefixWord ++ tailWord_2847702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2847705 : List Nat := [1, 2, 1, 2, 5, 1, 1, 2, 2, 3, 3]
def baseStart_2847705 : Nat := 118140960795 + 2847705 * 2 ^ 59
def prefixEnd_2847705 : Nat := 4983230072969 + 3 ^ 40 * 2847705 * 2
def baseEnd_2847705 : Nat := 1462241427211886074791149

theorem tailTrace_2847705 : CollatzResearch.WordTrace tailWord_2847705 prefixEnd_2847705 1462241427211886074791149 := by
  unfold tailWord_2847705
  simp only [CollatzResearch.WordTrace]
  refine ⟨103864334148258609138864569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69242889432172406092576379 103864334148258609138864569)
  ·
    refine ⟨77898250611193956854148427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103864334148258609138864569 77898250611193956854148427)
    ·
      refine ⟨116847375916790935281222641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77898250611193956854148427 116847375916790935281222641)
      ·
        refine ⟨87635531937593201460916981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 116847375916790935281222641 87635531937593201460916981)
        ·
          refine ⟨8215831119149362636960967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 87635531937593201460916981 8215831119149362636960967)
          ·
            refine ⟨12323746678724043955441451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8215831119149362636960967 12323746678724043955441451)
            ·
              refine ⟨18485620018086065933162177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12323746678724043955441451 18485620018086065933162177)
              ·
                refine ⟨13864215013564549449871633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18485620018086065933162177 13864215013564549449871633)
                ·
                  refine ⟨10398161260173412087403725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13864215013564549449871633 10398161260173412087403725)
                  ·
                    refine ⟨3899310472565029532776397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10398161260173412087403725 3899310472565029532776397)
                    ·
                      refine ⟨1462241427211886074791149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3899310472565029532776397 1462241427211886074791149)
                      ·
                        rfl

theorem cell23_2847705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 1, 2, 2, 3, 3].length) (baseStart_2847705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2847705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2847705 prefixEnd_2847705 := by exact prefixLift 2847705
  have htrace : WordTrace (prefixWord ++ tailWord_2847705) baseStart_2847705 baseEnd_2847705 := by
    simpa [prefixWord, tailWord_2847705, baseEnd_2847705] using wordTrace_append hprefix tailTrace_2847705
  have hstable : (prefixWord ++ tailWord_2847705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2847705).length < 2 ^ (prefixWord ++ tailWord_2847705).sum := by decide
  have hdescent : baseEnd_2847705 < baseStart_2847705 := by decide
  rcases family_descends (prefixWord ++ tailWord_2847705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2847706 : List Nat := [3, 1, 1, 2, 4, 3, 1, 2, 2, 2, 2]
def baseStart_2847706 : Nat := 118140960795 + 2847706 * 2 ^ 59
def prefixEnd_2847706 : Nat := 4983230072969 + 3 ^ 40 * 2847706 * 2
def baseEnd_2847706 : Nat := 1462241940692540570878645

theorem tailTrace_2847706 : CollatzResearch.WordTrace tailWord_2847706 prefixEnd_2847706 1462241940692540570878645 := by
  unfold tailWord_2847706
  simp only [CollatzResearch.WordTrace]
  refine ⟨25966092655313746577412743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69242913747503324206433981 25966092655313746577412743)
  ·
    refine ⟨38949138982970619866119115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25966092655313746577412743 38949138982970619866119115)
    ·
      refine ⟨58423708474455929799178673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38949138982970619866119115 58423708474455929799178673)
      ·
        refine ⟨43817781355841947349384005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58423708474455929799178673 43817781355841947349384005)
        ·
          refine ⟨8215834004220365128009501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 43817781355841947349384005 8215834004220365128009501)
          ·
            refine ⟨3080937751582636923003563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8215834004220365128009501 3080937751582636923003563)
            ·
              refine ⟨4621406627373955384505345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3080937751582636923003563 4621406627373955384505345)
              ·
                refine ⟨3466054970530466538379009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4621406627373955384505345 3466054970530466538379009)
                ·
                  refine ⟨2599541227897849903784257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3466054970530466538379009 2599541227897849903784257)
                  ·
                    refine ⟨1949655920923387427838193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2599541227897849903784257 1949655920923387427838193)
                    ·
                      refine ⟨1462241940692540570878645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1949655920923387427838193 1462241940692540570878645)
                      ·
                        rfl

theorem cell23_2847706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 3, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 3, 1, 2, 2, 2, 2].length) (baseStart_2847706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2847706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2847706 prefixEnd_2847706 := by exact prefixLift 2847706
  have htrace : WordTrace (prefixWord ++ tailWord_2847706) baseStart_2847706 baseEnd_2847706 := by
    simpa [prefixWord, tailWord_2847706, baseEnd_2847706] using wordTrace_append hprefix tailTrace_2847706
  have hstable : (prefixWord ++ tailWord_2847706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2847706).length < 2 ^ (prefixWord ++ tailWord_2847706).sum := by decide
  have hdescent : baseEnd_2847706 < baseStart_2847706 := by decide
  rcases family_descends (prefixWord ++ tailWord_2847706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2847745 : List Nat := [1, 2, 4, 1, 2, 2, 2, 1, 1, 3, 4]
def baseStart_2847745 : Nat := 118140960795 + 2847745 * 2 ^ 59
def prefixEnd_2847745 : Nat := 4983230072969 + 3 ^ 40 * 2847745 * 2
def baseEnd_2847745 : Nat := 1462261966438065918290965

theorem tailTrace_2847745 : CollatzResearch.WordTrace tailWord_2847745 prefixEnd_2847745 1462261966438065918290965 := by
  unfold tailWord_2847745
  simp only [CollatzResearch.WordTrace]
  refine ⟨103865793068113695970320689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69243862045409130646880459 103865793068113695970320689)
  ·
    refine ⟨77899344801085271977740517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103865793068113695970320689 77899344801085271977740517)
    ·
      refine ⟨14606127150203488495826347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 77899344801085271977740517 14606127150203488495826347)
      ·
        refine ⟨21909190725305232743739521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14606127150203488495826347 21909190725305232743739521)
        ·
          refine ⟨16431893043978924557804641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21909190725305232743739521 16431893043978924557804641)
          ·
            refine ⟨12323919782984193418353481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16431893043978924557804641 12323919782984193418353481)
            ·
              refine ⟨9242939837238145063765111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12323919782984193418353481 9242939837238145063765111)
              ·
                refine ⟨13864409755857217595647667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9242939837238145063765111 13864409755857217595647667)
                ·
                  refine ⟨20796614633785826393471501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13864409755857217595647667 20796614633785826393471501)
                  ·
                    refine ⟨7798730487669684897551813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20796614633785826393471501 7798730487669684897551813)
                    ·
                      refine ⟨1462261966438065918290965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7798730487669684897551813 1462261966438065918290965)
                      ·
                        rfl

theorem cell23_2847745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 2, 1, 1, 3, 4].length) (baseStart_2847745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2847745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2847745 prefixEnd_2847745 := by exact prefixLift 2847745
  have htrace : WordTrace (prefixWord ++ tailWord_2847745) baseStart_2847745 baseEnd_2847745 := by
    simpa [prefixWord, tailWord_2847745, baseEnd_2847745] using wordTrace_append hprefix tailTrace_2847745
  have hstable : (prefixWord ++ tailWord_2847745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2847745).length < 2 ^ (prefixWord ++ tailWord_2847745).sum := by decide
  have hdescent : baseEnd_2847745 < baseStart_2847745 := by decide
  rcases family_descends (prefixWord ++ tailWord_2847745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2847852 : List Nat := [2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 4]
def baseStart_2847852 : Nat := 118140960795 + 2847852 * 2 ^ 59
def prefixEnd_2847852 : Nat := 4983230072969 + 3 ^ 40 * 2847852 * 2
def baseEnd_2847852 : Nat := 1462316908868096999652973

theorem tailTrace_2847852 : CollatzResearch.WordTrace tailWord_2847852 prefixEnd_2847852 1462316908868096999652973 := by
  unfold tailWord_2847852
  simp only [CollatzResearch.WordTrace]
  refine ⟨51934847839363026622232905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69246463785817368829643873 51934847839363026622232905)
  ·
    refine ⟨38951135879522269966674679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51934847839363026622232905 38951135879522269966674679)
    ·
      refine ⟨58426703819283404950012019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38951135879522269966674679 58426703819283404950012019)
      ·
        refine ⟨87640055728925107425018029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58426703819283404950012019 87640055728925107425018029)
        ·
          refine ⟨32865020898346915284381761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 87640055728925107425018029 32865020898346915284381761)
          ·
            refine ⟨24648765673760186463286321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32865020898346915284381761 24648765673760186463286321)
            ·
              refine ⟨18486574255320139847464741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24648765673760186463286321 18486574255320139847464741)
              ·
                refine ⟨3466232672872526221399639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18486574255320139847464741 3466232672872526221399639)
                ·
                  refine ⟨5199349009308789332099459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3466232672872526221399639 5199349009308789332099459)
                  ·
                    refine ⟨7799023513963183998149189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5199349009308789332099459 7799023513963183998149189)
                    ·
                      refine ⟨1462316908868096999652973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7799023513963183998149189 1462316908868096999652973)
                      ·
                        rfl

theorem cell23_2847852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 4].length) (baseStart_2847852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2847852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2847852 prefixEnd_2847852 := by exact prefixLift 2847852
  have htrace : WordTrace (prefixWord ++ tailWord_2847852) baseStart_2847852 baseEnd_2847852 := by
    simpa [prefixWord, tailWord_2847852, baseEnd_2847852] using wordTrace_append hprefix tailTrace_2847852
  have hstable : (prefixWord ++ tailWord_2847852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2847852).length < 2 ^ (prefixWord ++ tailWord_2847852).sum := by decide
  have hdescent : baseEnd_2847852 < baseStart_2847852 := by decide
  rcases family_descends (prefixWord ++ tailWord_2847852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2847862 : List Nat := [5, 1, 1, 2, 1, 1, 1, 4, 1, 6]
def baseStart_2847862 : Nat := 118140960795 + 2847862 * 2 ^ 59
def prefixEnd_2847862 : Nat := 4983230072969 + 3 ^ 40 * 2847862 * 2
def baseEnd_2847862 : Nat := 487440681224880653509309

theorem tailTrace_2847862 : CollatzResearch.WordTrace tailWord_2847862 prefixEnd_2847862 487440681224880653509309 := by
  unfold tailWord_2847862
  simp only [CollatzResearch.WordTrace]
  refine ⟨6491878775543114059520615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 69246706939126549968219893 6491878775543114059520615)
  ·
    refine ⟨9737818163314671089280923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6491878775543114059520615 9737818163314671089280923)
    ·
      refine ⟨14606727244972006633921385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9737818163314671089280923 14606727244972006633921385)
      ·
        refine ⟨10955045433729004975441039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14606727244972006633921385 10955045433729004975441039)
        ·
          refine ⟨16432568150593507463161559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10955045433729004975441039 16432568150593507463161559)
          ·
            refine ⟨24648852225890261194742339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16432568150593507463161559 24648852225890261194742339)
            ·
              refine ⟨36973278338835391792113509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24648852225890261194742339 36973278338835391792113509)
              ·
                refine ⟨6932489688531635961021283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36973278338835391792113509 6932489688531635961021283)
                ·
                  refine ⟨10398734532797453941531925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6932489688531635961021283 10398734532797453941531925)
                  ·
                    refine ⟨487440681224880653509309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10398734532797453941531925 487440681224880653509309)
                    ·
                      rfl

theorem cell23_2847862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 4, 1, 6].length) (baseStart_2847862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2847862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2847862 prefixEnd_2847862 := by exact prefixLift 2847862
  have htrace : WordTrace (prefixWord ++ tailWord_2847862) baseStart_2847862 baseEnd_2847862 := by
    simpa [prefixWord, tailWord_2847862, baseEnd_2847862] using wordTrace_append hprefix tailTrace_2847862
  have hstable : (prefixWord ++ tailWord_2847862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2847862).length < 2 ^ (prefixWord ++ tailWord_2847862).sum := by decide
  have hdescent : baseEnd_2847862 < baseStart_2847862 := by decide
  rcases family_descends (prefixWord ++ tailWord_2847862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2847869 : List Nat := [1, 4, 1, 1, 3, 1, 1, 2, 5, 2, 2]
def baseStart_2847869 : Nat := 118140960795 + 2847869 * 2 ^ 59
def prefixEnd_2847869 : Nat := 4983230072969 + 3 ^ 40 * 2847869 * 2
def baseEnd_2847869 : Nat := 1462325638039223433140395

theorem tailTrace_2847869 : CollatzResearch.WordTrace tailWord_2847869 prefixEnd_2847869 1462325638039223433140395 := by
  unfold tailWord_2847869
  simp only [CollatzResearch.WordTrace]
  refine ⟨103870315719664465147834661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69246877146442976765223107 103870315719664465147834661)
  ·
    refine ⟨19475684197437087215218999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 103870315719664465147834661 19475684197437087215218999)
    ·
      refine ⟨29213526296155630822828499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19475684197437087215218999 29213526296155630822828499)
      ·
        refine ⟨43820289444233446234242749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29213526296155630822828499 43820289444233446234242749)
        ·
          refine ⟨16432608541587542337841031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43820289444233446234242749 16432608541587542337841031)
          ·
            refine ⟨24648912812381313506761547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16432608541587542337841031 24648912812381313506761547)
            ·
              refine ⟨36973369218571970260142321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24648912812381313506761547 36973369218571970260142321)
              ·
                refine ⟨27730026913928977695106741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36973369218571970260142321 27730026913928977695106741)
                ·
                  refine ⟨2599690023180841658916257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 27730026913928977695106741 2599690023180841658916257)
                  ·
                    refine ⟨1949767517385631244187193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2599690023180841658916257 1949767517385631244187193)
                    ·
                      refine ⟨1462325638039223433140395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1949767517385631244187193 1462325638039223433140395)
                      ·
                        rfl

theorem cell23_2847869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 2, 5, 2, 2].length) (baseStart_2847869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2847869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2847869 prefixEnd_2847869 := by exact prefixLift 2847869
  have htrace : WordTrace (prefixWord ++ tailWord_2847869) baseStart_2847869 baseEnd_2847869 := by
    simpa [prefixWord, tailWord_2847869, baseEnd_2847869] using wordTrace_append hprefix tailTrace_2847869
  have hstable : (prefixWord ++ tailWord_2847869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2847869).length < 2 ^ (prefixWord ++ tailWord_2847869).sum := by decide
  have hdescent : baseEnd_2847869 < baseStart_2847869 := by decide
  rcases family_descends (prefixWord ++ tailWord_2847869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2847870 : List Nat := [4, 2, 4, 1, 2, 1, 1, 2, 6]
def baseStart_2847870 : Nat := 118140960795 + 2847870 * 2 ^ 59
def prefixEnd_2847870 : Nat := 4983230072969 + 3 ^ 40 * 2847870 * 2
def baseEnd_2847870 : Nat := 162480683502208658803099

theorem tailTrace_2847870 : CollatzResearch.WordTrace tailWord_2847870 prefixEnd_2847870 162480683502208658803099 := by
  unfold tailWord_2847870
  simp only [CollatzResearch.WordTrace]
  refine ⟨12983794024082605289827633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 69246901461773894879080709 12983794024082605289827633)
  ·
    refine ⟨9737845518061953967370725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12983794024082605289827633 9737845518061953967370725)
    ·
      refine ⟨1825846034636616368882011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9737845518061953967370725 1825846034636616368882011)
      ·
        refine ⟨2738769051954924553323017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1825846034636616368882011 2738769051954924553323017)
        ·
          refine ⟨2054076788966193414992263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2738769051954924553323017 2054076788966193414992263)
          ·
            refine ⟨3081115183449290122488395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2054076788966193414992263 3081115183449290122488395)
            ·
              refine ⟨4621672775173935183732593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3081115183449290122488395 4621672775173935183732593)
              ·
                refine ⟨3466254581380451387799445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4621672775173935183732593 3466254581380451387799445)
                ·
                  refine ⟨162480683502208658803099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3466254581380451387799445 162480683502208658803099)
                  ·
                    rfl

theorem cell23_2847870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 2, 1, 1, 2, 6].length) (baseStart_2847870 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2847870 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2847870 prefixEnd_2847870 := by exact prefixLift 2847870
  have htrace : WordTrace (prefixWord ++ tailWord_2847870) baseStart_2847870 baseEnd_2847870 := by
    simpa [prefixWord, tailWord_2847870, baseEnd_2847870] using wordTrace_append hprefix tailTrace_2847870
  have hstable : (prefixWord ++ tailWord_2847870).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2847870).length < 2 ^ (prefixWord ++ tailWord_2847870).sum := by decide
  have hdescent : baseEnd_2847870 < baseStart_2847870 := by decide
  rcases family_descends (prefixWord ++ tailWord_2847870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2847886 : List Nat := [4, 1, 1, 3, 2, 1, 1, 3, 3, 2, 2]
def baseStart_2847886 : Nat := 118140960795 + 2847886 * 2 ^ 59
def prefixEnd_2847886 : Nat := 4983230072969 + 3 ^ 40 * 2847886 * 2
def baseEnd_2847886 : Nat := 1462334367210349866627817

theorem tailTrace_2847886 : CollatzResearch.WordTrace tailWord_2847886 prefixEnd_2847886 1462334367210349866627817 := by
  unfold tailWord_2847886
  simp only [CollatzResearch.WordTrace]
  refine ⟨12983866970075359631400439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 69247290507068584700802341 12983866970075359631400439)
  ·
    refine ⟨19475800455113039447100659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12983866970075359631400439 19475800455113039447100659)
    ·
      refine ⟨29213700682669559170650989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19475800455113039447100659 29213700682669559170650989)
      ·
        refine ⟨10955137756001084688994121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29213700682669559170650989 10955137756001084688994121)
        ·
          refine ⟨8216353317000813516745591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10955137756001084688994121 8216353317000813516745591)
          ·
            refine ⟨12324529975501220275118387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8216353317000813516745591 12324529975501220275118387)
            ·
              refine ⟨18486794963251830412677581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12324529975501220275118387 18486794963251830412677581)
              ·
                refine ⟨6932548111219436404754093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18486794963251830412677581 6932548111219436404754093)
                ·
                  refine ⟨2599705541707288651782785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6932548111219436404754093 2599705541707288651782785)
                  ·
                    refine ⟨1949779156280466488837089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2599705541707288651782785 1949779156280466488837089)
                    ·
                      refine ⟨1462334367210349866627817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1949779156280466488837089 1462334367210349866627817)
                      ·
                        rfl

theorem cell23_2847886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 1, 3, 3, 2, 2].length) (baseStart_2847886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2847886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2847886 prefixEnd_2847886 := by exact prefixLift 2847886
  have htrace : WordTrace (prefixWord ++ tailWord_2847886) baseStart_2847886 baseEnd_2847886 := by
    simpa [prefixWord, tailWord_2847886, baseEnd_2847886] using wordTrace_append hprefix tailTrace_2847886
  have hstable : (prefixWord ++ tailWord_2847886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2847886).length < 2 ^ (prefixWord ++ tailWord_2847886).sum := by decide
  have hdescent : baseEnd_2847886 < baseStart_2847886 := by decide
  rcases family_descends (prefixWord ++ tailWord_2847886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2847896 : List Nat := [2, 1, 2, 4, 2, 2, 3, 1, 2, 4]
def baseStart_2847896 : Nat := 118140960795 + 2847896 * 2 ^ 59
def prefixEnd_2847896 : Nat := 4983230072969 + 3 ^ 40 * 2847896 * 2
def baseEnd_2847896 : Nat := 487446500672298275834257

theorem tailTrace_2847896 : CollatzResearch.WordTrace tailWord_2847896 prefixEnd_2847896 487446500672298275834257 := by
  unfold tailWord_2847896
  simp only [CollatzResearch.WordTrace]
  refine ⟨51935650245283324379533771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69247533660377765839378361 51935650245283324379533771)
  ·
    refine ⟨77903475367924986569300657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51935650245283324379533771 77903475367924986569300657)
    ·
      refine ⟨58427606525943739926975493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77903475367924986569300657 58427606525943739926975493)
      ·
        refine ⟨10955176223614451236307905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 58427606525943739926975493 10955176223614451236307905)
        ·
          refine ⟨8216382167710838427230929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10955176223614451236307905 8216382167710838427230929)
          ·
            refine ⟨6162286625783128820423197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8216382167710838427230929 6162286625783128820423197)
            ·
              refine ⟨2310857484668673307658699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6162286625783128820423197 2310857484668673307658699)
              ·
                refine ⟨3466286227003009961488049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2310857484668673307658699 3466286227003009961488049)
                ·
                  refine ⟨2599714670252257471116037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3466286227003009961488049 2599714670252257471116037)
                  ·
                    refine ⟨487446500672298275834257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2599714670252257471116037 487446500672298275834257)
                    ·
                      rfl

theorem cell23_2847896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 3, 1, 2, 4].length) (baseStart_2847896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2847896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2847896 prefixEnd_2847896 := by exact prefixLift 2847896
  have htrace : WordTrace (prefixWord ++ tailWord_2847896) baseStart_2847896 baseEnd_2847896 := by
    simpa [prefixWord, tailWord_2847896, baseEnd_2847896] using wordTrace_append hprefix tailTrace_2847896
  have hstable : (prefixWord ++ tailWord_2847896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2847896).length < 2 ^ (prefixWord ++ tailWord_2847896).sum := by decide
  have hdescent : baseEnd_2847896 < baseStart_2847896 := by decide
  rcases family_descends (prefixWord ++ tailWord_2847896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2847926 : List Nat := [5, 1, 3, 2, 1, 2, 9]
def baseStart_2847926 : Nat := 118140960795 + 2847926 * 2 ^ 59
def prefixEnd_2847926 : Nat := 4983230072969 + 3 ^ 40 * 2847926 * 2
def baseEnd_2847926 : Nat := 18053764276994193952193

theorem tailTrace_2847926 : CollatzResearch.WordTrace tailWord_2847926 prefixEnd_2847926 18053764276994193952193 := by
  unfold tailWord_2847926
  simp only [CollatzResearch.WordTrace]
  refine ⟨6492024667528622742666227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 69248263120305309255106421 6492024667528622742666227)
  ·
    refine ⟨9738037001292934113999341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6492024667528622742666227 9738037001292934113999341)
    ·
      refine ⟨3651763875484850292749753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9738037001292934113999341 3651763875484850292749753)
      ·
        refine ⟨2738822906613637719562315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3651763875484850292749753 2738822906613637719562315)
        ·
          refine ⟨4108234359920456579343473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2738822906613637719562315 4108234359920456579343473)
          ·
            refine ⟨3081175769940342434507605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4108234359920456579343473 3081175769940342434507605)
            ·
              refine ⟨18053764276994193952193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3081175769940342434507605 18053764276994193952193)
              ·
                rfl

theorem cell23_2847926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 2, 9].length) (baseStart_2847926 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2847926 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2847926 prefixEnd_2847926 := by exact prefixLift 2847926
  have htrace : WordTrace (prefixWord ++ tailWord_2847926) baseStart_2847926 baseEnd_2847926 := by
    simpa [prefixWord, tailWord_2847926, baseEnd_2847926] using wordTrace_append hprefix tailTrace_2847926
  have hstable : (prefixWord ++ tailWord_2847926).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2847926).length < 2 ^ (prefixWord ++ tailWord_2847926).sum := by decide
  have hdescent : baseEnd_2847926 < baseStart_2847926 := by decide
  rcases family_descends (prefixWord ++ tailWord_2847926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2847935 : List Nat := [1, 1, 2, 2, 2, 2, 2, 1, 4, 6]
def baseStart_2847935 : Nat := 118140960795 + 2847935 * 2 ^ 59
def prefixEnd_2847935 : Nat := 4983230072969 + 3 ^ 40 * 2847935 * 2
def baseEnd_2847935 : Nat := 487453175920806724971697

theorem tailTrace_2847935 : CollatzResearch.WordTrace tailWord_2847935 prefixEnd_2847935 487453175920806724971697 := by
  unfold tailWord_2847935
  simp only [CollatzResearch.WordTrace]
  refine ⟨103872722937425358419737259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69248481958283572279824839 103872722937425358419737259)
  ·
    refine ⟨155809084406138037629605889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103872722937425358419737259 155809084406138037629605889)
    ·
      refine ⟨116856813304603528222204417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 155809084406138037629605889 116856813304603528222204417)
      ·
        refine ⟨87642609978452646166653313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 116856813304603528222204417 87642609978452646166653313)
        ·
          refine ⟨65731957483839484624989985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87642609978452646166653313 65731957483839484624989985)
          ·
            refine ⟨49298968112879613468742489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65731957483839484624989985 49298968112879613468742489)
            ·
              refine ⟨36974226084659710101556867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49298968112879613468742489 36974226084659710101556867)
              ·
                refine ⟨55461339126989565152335301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36974226084659710101556867 55461339126989565152335301)
                ·
                  refine ⟨10399001086310543466062869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 55461339126989565152335301 10399001086310543466062869)
                  ·
                    refine ⟨487453175920806724971697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10399001086310543466062869 487453175920806724971697)
                    ·
                      rfl

theorem cell23_2847935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 1, 4, 6].length) (baseStart_2847935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2847935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2847935 prefixEnd_2847935 := by exact prefixLift 2847935
  have htrace : WordTrace (prefixWord ++ tailWord_2847935) baseStart_2847935 baseEnd_2847935 := by
    simpa [prefixWord, tailWord_2847935, baseEnd_2847935] using wordTrace_append hprefix tailTrace_2847935
  have hstable : (prefixWord ++ tailWord_2847935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2847935).length < 2 ^ (prefixWord ++ tailWord_2847935).sum := by decide
  have hdescent : baseEnd_2847935 < baseStart_2847935 := by decide
  rcases family_descends (prefixWord ++ tailWord_2847935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2847937 : List Nat := [1, 2, 6, 1, 1, 2, 3, 2, 1, 2, 2]
def baseStart_2847937 : Nat := 118140960795 + 2847937 * 2 ^ 59
def prefixEnd_2847937 : Nat := 4983230072969 + 3 ^ 40 * 2847937 * 2
def baseEnd_2847937 : Nat := 1462360554723729167090083

theorem tailTrace_2847937 : CollatzResearch.WordTrace tailWord_2847937 prefixEnd_2847937 1462360554723729167090083 := by
  unfold tailWord_2847937
  simp only [CollatzResearch.WordTrace]
  refine ⟨103872795883418112761310065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69248530588945408507540043 103872795883418112761310065)
  ·
    refine ⟨77904596912563584570982549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103872795883418112761310065 77904596912563584570982549)
    ·
      refine ⟨3651777980276418026764807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 77904596912563584570982549 3651777980276418026764807)
      ·
        refine ⟨5477666970414627040147211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3651777980276418026764807 5477666970414627040147211)
        ·
          refine ⟨8216500455621940560220817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5477666970414627040147211 8216500455621940560220817)
          ·
            refine ⟨6162375341716455420165613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8216500455621940560220817 6162375341716455420165613)
            ·
              refine ⟨2310890753143670782562105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6162375341716455420165613 2310890753143670782562105)
              ·
                refine ⟨1733168064857753086921579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2310890753143670782562105 1733168064857753086921579)
                ·
                  refine ⟨2599752097286629630382369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1733168064857753086921579 2599752097286629630382369)
                  ·
                    refine ⟨1949814072964972222786777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2599752097286629630382369 1949814072964972222786777)
                    ·
                      refine ⟨1462360554723729167090083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1949814072964972222786777 1462360554723729167090083)
                      ·
                        rfl

theorem cell23_2847937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 3, 2, 1, 2, 2].length) (baseStart_2847937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2847937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2847937 prefixEnd_2847937 := by exact prefixLift 2847937
  have htrace : WordTrace (prefixWord ++ tailWord_2847937) baseStart_2847937 baseEnd_2847937 := by
    simpa [prefixWord, tailWord_2847937, baseEnd_2847937] using wordTrace_append hprefix tailTrace_2847937
  have hstable : (prefixWord ++ tailWord_2847937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2847937).length < 2 ^ (prefixWord ++ tailWord_2847937).sum := by decide
  have hdescent : baseEnd_2847937 < baseStart_2847937 := by decide
  rcases family_descends (prefixWord ++ tailWord_2847937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2847988 : List Nat := [2, 6, 1, 2, 2, 1, 2, 2, 1, 2, 2]
def baseStart_2847988 : Nat := 118140960795 + 2847988 * 2 ^ 59
def prefixEnd_2847988 : Nat := 4983230072969 + 3 ^ 40 * 2847988 * 2
def baseEnd_2847988 : Nat := 1462386742237108467552349

theorem tailTrace_2847988 : CollatzResearch.WordTrace tailWord_2847988 prefixEnd_2847988 1462386742237108467552349 := by
  unfold tailWord_2847988
  simp only [CollatzResearch.WordTrace]
  refine ⟨51937328003116674235708309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69249770670822232314277745 51937328003116674235708309)
  ·
    refine ⟨2434562250146094104798827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 51937328003116674235708309 2434562250146094104798827)
    ·
      refine ⟨3651843375219141157198241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2434562250146094104798827 3651843375219141157198241)
      ·
        refine ⟨2738882531414355867898681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3651843375219141157198241 2738882531414355867898681)
        ·
          refine ⟨2054161898560766900924011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2738882531414355867898681 2054161898560766900924011)
          ·
            refine ⟨3081242847841150351386017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2054161898560766900924011 3081242847841150351386017)
            ·
              refine ⟨2310932135880862763539513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3081242847841150351386017 2310932135880862763539513)
              ·
                refine ⟨1733199101910647072654635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2310932135880862763539513 1733199101910647072654635)
                ·
                  refine ⟨2599798652865970608981953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1733199101910647072654635 2599798652865970608981953)
                  ·
                    refine ⟨1949848989649477956736465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2599798652865970608981953 1949848989649477956736465)
                    ·
                      refine ⟨1462386742237108467552349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1949848989649477956736465 1462386742237108467552349)
                      ·
                        rfl

theorem cell23_2847988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 2, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 2, 1, 2, 2, 1, 2, 2].length) (baseStart_2847988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2847988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2847988 prefixEnd_2847988 := by exact prefixLift 2847988
  have htrace : WordTrace (prefixWord ++ tailWord_2847988) baseStart_2847988 baseEnd_2847988 := by
    simpa [prefixWord, tailWord_2847988, baseEnd_2847988] using wordTrace_append hprefix tailTrace_2847988
  have hstable : (prefixWord ++ tailWord_2847988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2847988).length < 2 ^ (prefixWord ++ tailWord_2847988).sum := by decide
  have hdescent : baseEnd_2847988 < baseStart_2847988 := by decide
  rcases family_descends (prefixWord ++ tailWord_2847988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2847999 : List Nat := [1, 1, 2, 2, 1, 6, 1, 4, 5]
def baseStart_2847999 : Nat := 118140960795 + 2847999 * 2 ^ 59
def prefixEnd_2847999 : Nat := 4983230072969 + 3 ^ 40 * 2847999 * 2
def baseEnd_2847999 : Nat := 162488043391589769390533

theorem tailTrace_2847999 : CollatzResearch.WordTrace tailWord_2847999 prefixEnd_2847999 162488043391589769390533 := by
  unfold tailWord_2847999
  simp only [CollatzResearch.WordTrace]
  refine ⟨103875057209193497350067051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69250038139462331566711367 103875057209193497350067051)
  ·
    refine ⟨155812585813790246025100577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103875057209193497350067051 155812585813790246025100577)
    ·
      refine ⟨116859439360342684518825433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 155812585813790246025100577 116859439360342684518825433)
      ·
        refine ⟨87644579520257013389119075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 116859439360342684518825433 87644579520257013389119075)
        ·
          refine ⟨131466869280385520083678613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87644579520257013389119075 131466869280385520083678613)
          ·
            refine ⟨6162509497518071253922435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 131466869280385520083678613 6162509497518071253922435)
            ·
              refine ⟨9243764246277106880883653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6162509497518071253922435 9243764246277106880883653)
              ·
                refine ⟨1733205796176957540165685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9243764246277106880883653 1733205796176957540165685)
                ·
                  refine ⟨162488043391589769390533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1733205796176957540165685 162488043391589769390533)
                  ·
                    rfl

theorem cell23_2847999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 1, 4, 5].length) (baseStart_2847999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2847999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2847999 prefixEnd_2847999 := by exact prefixLift 2847999
  have htrace : WordTrace (prefixWord ++ tailWord_2847999) baseStart_2847999 baseEnd_2847999 := by
    simpa [prefixWord, tailWord_2847999, baseEnd_2847999] using wordTrace_append hprefix tailTrace_2847999
  have hstable : (prefixWord ++ tailWord_2847999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2847999).length < 2 ^ (prefixWord ++ tailWord_2847999).sum := by decide
  have hdescent : baseEnd_2847999 < baseStart_2847999 := by decide
  rcases family_descends (prefixWord ++ tailWord_2847999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2848029 : List Nat := [1, 4, 2, 3, 1, 2, 1, 1, 1, 7]
def baseStart_2848029 : Nat := 118140960795 + 2848029 * 2 ^ 59
def prefixEnd_2848029 : Nat := 4983230072969 + 3 ^ 40 * 2848029 * 2
def baseEnd_2848029 : Nat := 487469264981314269046553

theorem tailTrace_2848029 : CollatzResearch.WordTrace tailWord_2848029 prefixEnd_2848029 487469264981314269046553 := by
  unfold tailWord_2848029
  simp only [CollatzResearch.WordTrace]
  refine ⟨103876151399084812473659141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69250767599389874982439427 103876151399084812473659141)
  ·
    refine ⟨19476778387328402338811089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 103876151399084812473659141 19476778387328402338811089)
    ·
      refine ⟨14607583790496301754108317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19476778387328402338811089 14607583790496301754108317)
      ·
        refine ⟨5477843921436113157790619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14607583790496301754108317 5477843921436113157790619)
        ·
          refine ⟨8216765882154169736685929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5477843921436113157790619 8216765882154169736685929)
          ·
            refine ⟨6162574411615627302514447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8216765882154169736685929 6162574411615627302514447)
            ·
              refine ⟨9243861617423440953771671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6162574411615627302514447 9243861617423440953771671)
              ·
                refine ⟨13865792426135161430657507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9243861617423440953771671 13865792426135161430657507)
                ·
                  refine ⟨20798688639202742145986261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13865792426135161430657507 20798688639202742145986261)
                  ·
                    refine ⟨487469264981314269046553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 20798688639202742145986261 487469264981314269046553)
                    ·
                      rfl

theorem cell23_2848029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 1, 1, 1, 7].length) (baseStart_2848029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2848029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2848029 prefixEnd_2848029 := by exact prefixLift 2848029
  have htrace : WordTrace (prefixWord ++ tailWord_2848029) baseStart_2848029 baseEnd_2848029 := by
    simpa [prefixWord, tailWord_2848029, baseEnd_2848029] using wordTrace_append hprefix tailTrace_2848029
  have hstable : (prefixWord ++ tailWord_2848029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2848029).length < 2 ^ (prefixWord ++ tailWord_2848029).sum := by decide
  have hdescent : baseEnd_2848029 < baseStart_2848029 := by decide
  rcases family_descends (prefixWord ++ tailWord_2848029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2848110 : List Nat := [4, 1, 2, 4, 1, 2, 1, 1, 3, 4]
def baseStart_2848110 : Nat := 118140960795 + 2848110 * 2 ^ 59
def prefixEnd_2848110 : Nat := 4983230072969 + 3 ^ 40 * 2848110 * 2
def baseEnd_2848110 : Nat := 487483128958985663408929

theorem tailTrace_2848110 : CollatzResearch.WordTrace tailWord_2848110 prefixEnd_2848110 487483128958985663408929 := by
  unfold tailWord_2848110
  simp only [CollatzResearch.WordTrace]
  refine ⟨12984888213973920413419723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 69252737141194242204905189 12984888213973920413419723)
  ·
    refine ⟨19477332320960880620129585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12984888213973920413419723 19477332320960880620129585)
    ·
      refine ⟨14607999240720660465097189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19477332320960880620129585 14607999240720660465097189)
      ·
        refine ⟨2738999857635123837205723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14607999240720660465097189 2738999857635123837205723)
        ·
          refine ⟨4108499786452685755808585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2738999857635123837205723 4108499786452685755808585)
          ·
            refine ⟨3081374839839514316856439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4108499786452685755808585 3081374839839514316856439)
            ·
              refine ⟨4622062259759271475284659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3081374839839514316856439 4622062259759271475284659)
              ·
                refine ⟨6933093389638907212926989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4622062259759271475284659 6933093389638907212926989)
                ·
                  refine ⟨2599910021114590204847621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6933093389638907212926989 2599910021114590204847621)
                  ·
                    refine ⟨487483128958985663408929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2599910021114590204847621 487483128958985663408929)
                    ·
                      rfl

theorem cell23_2848110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 2, 1, 1, 3, 4].length) (baseStart_2848110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2848110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2848110 prefixEnd_2848110 := by exact prefixLift 2848110
  have htrace : WordTrace (prefixWord ++ tailWord_2848110) baseStart_2848110 baseEnd_2848110 := by
    simpa [prefixWord, tailWord_2848110, baseEnd_2848110] using wordTrace_append hprefix tailTrace_2848110
  have hstable : (prefixWord ++ tailWord_2848110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2848110).length < 2 ^ (prefixWord ++ tailWord_2848110).sum := by decide
  have hdescent : baseEnd_2848110 < baseStart_2848110 := by decide
  rcases family_descends (prefixWord ++ tailWord_2848110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2848136 : List Nat := [2, 1, 3, 3, 1, 2, 3, 2, 1, 5]
def baseStart_2848136 : Nat := 118140960795 + 2848136 * 2 ^ 59
def prefixEnd_2848136 : Nat := 4983230072969 + 3 ^ 40 * 2848136 * 2
def baseEnd_2848136 : Nat := 487487579124657962833889

theorem tailTrace_2848136 : CollatzResearch.WordTrace tailWord_2848136 prefixEnd_2848136 487487579124657962833889 := by
  unfold tailWord_2848136
  simp only [CollatzResearch.WordTrace]
  refine ⟨51940027004848584873902131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69253369339798113165202841 51940027004848584873902131)
  ·
    refine ⟨77910040507272877310853197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51940027004848584873902131 77910040507272877310853197)
    ·
      refine ⟨29216265190227328991569949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 77910040507272877310853197 29216265190227328991569949)
      ·
        refine ⟨10956099446335248371838731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29216265190227328991569949 10956099446335248371838731)
        ·
          refine ⟨16434149169502872557758097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10956099446335248371838731 16434149169502872557758097)
          ·
            refine ⟨12325611877127154418318573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16434149169502872557758097 12325611877127154418318573)
            ·
              refine ⟨4622104453922682906869465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12325611877127154418318573 4622104453922682906869465)
              ·
                refine ⟨3466578340442012180152099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4622104453922682906869465 3466578340442012180152099)
                ·
                  refine ⟨5199867510663018270228149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3466578340442012180152099 5199867510663018270228149)
                  ·
                    refine ⟨487487579124657962833889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5199867510663018270228149 487487579124657962833889)
                    ·
                      rfl

theorem cell23_2848136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 3, 2, 1, 5].length) (baseStart_2848136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2848136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2848136 prefixEnd_2848136 := by exact prefixLift 2848136
  have htrace : WordTrace (prefixWord ++ tailWord_2848136) baseStart_2848136 baseEnd_2848136 := by
    simpa [prefixWord, tailWord_2848136, baseEnd_2848136] using wordTrace_append hprefix tailTrace_2848136
  have hstable : (prefixWord ++ tailWord_2848136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2848136).length < 2 ^ (prefixWord ++ tailWord_2848136).sum := by decide
  have hdescent : baseEnd_2848136 < baseStart_2848136 := by decide
  rcases family_descends (prefixWord ++ tailWord_2848136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2848139 : List Nat := [1, 1, 1, 1, 4, 3, 3, 1, 3, 1, 4]
def baseStart_2848139 : Nat := 118140960795 + 2848139 * 2 ^ 59
def prefixEnd_2848139 : Nat := 4983230072969 + 3 ^ 40 * 2848139 * 2
def baseEnd_2848139 : Nat := 1462464277815937376764153

theorem tailTrace_2848139 : CollatzResearch.WordTrace tailWord_2848139 prefixEnd_2848139 1462464277815937376764153 := by
  unfold tailWord_2848139
  simp only [CollatzResearch.WordTrace]
  refine ⟨103880163428686301260163471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69253442285790867506775647 103880163428686301260163471)
  ·
    refine ⟨155820245143029451890245207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103880163428686301260163471 155820245143029451890245207)
    ·
      refine ⟨233730367714544177835367811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155820245143029451890245207 233730367714544177835367811)
      ·
        refine ⟨350595551571816266753051717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 233730367714544177835367811 350595551571816266753051717)
        ·
          refine ⟨65736665919715550016197197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 350595551571816266753051717 65736665919715550016197197)
          ·
            refine ⟨24651249719893331256073949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 65736665919715550016197197 24651249719893331256073949)
            ·
              refine ⟨9244218644959999221027731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24651249719893331256073949 9244218644959999221027731)
              ·
                refine ⟨13866327967439998831541597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9244218644959999221027731 13866327967439998831541597)
                ·
                  refine ⟨5199872987789999561828099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13866327967439998831541597 5199872987789999561828099)
                  ·
                    refine ⟨7799809481684999342742149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5199872987789999561828099 7799809481684999342742149)
                    ·
                      refine ⟨1462464277815937376764153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7799809481684999342742149 1462464277815937376764153)
                      ·
                        rfl

theorem cell23_2848139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 3, 1, 3, 1, 4].length) (baseStart_2848139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2848139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2848139 prefixEnd_2848139 := by exact prefixLift 2848139
  have htrace : WordTrace (prefixWord ++ tailWord_2848139) baseStart_2848139 baseEnd_2848139 := by
    simpa [prefixWord, tailWord_2848139, baseEnd_2848139] using wordTrace_append hprefix tailTrace_2848139
  have hstable : (prefixWord ++ tailWord_2848139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2848139).length < 2 ^ (prefixWord ++ tailWord_2848139).sum := by decide
  have hdescent : baseEnd_2848139 < baseStart_2848139 := by decide
  rcases family_descends (prefixWord ++ tailWord_2848139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2848149 : List Nat := [1, 3, 2, 1, 1, 2, 2, 1, 6, 4]
def baseStart_2848149 : Nat := 118140960795 + 2848149 * 2 ^ 59
def prefixEnd_2848149 : Nat := 4983230072969 + 3 ^ 40 * 2848149 * 2
def baseEnd_2848149 : Nat := 487489804207494112546369

theorem tailTrace_2848149 : CollatzResearch.WordTrace tailWord_2848149 prefixEnd_2848149 487489804207494112546369 := by
  unfold tailWord_2848149
  simp only [CollatzResearch.WordTrace]
  refine ⟨103880528158650072968027501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69253685439100048645351667 103880528158650072968027501)
  ·
    refine ⟨38955198059493777363010313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 103880528158650072968027501 38955198059493777363010313)
    ·
      refine ⟨29216398544620333022257735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38955198059493777363010313 29216398544620333022257735)
      ·
        refine ⟨43824597816930499533386603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29216398544620333022257735 43824597816930499533386603)
        ·
          refine ⟨65736896725395749300079905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43824597816930499533386603 65736896725395749300079905)
          ·
            refine ⟨49302672544046811975059929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65736896725395749300079905 49302672544046811975059929)
            ·
              refine ⟨36977004408035108981294947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49302672544046811975059929 36977004408035108981294947)
              ·
                refine ⟨55465506612052663471942421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36977004408035108981294947 55465506612052663471942421)
                ·
                  refine ⟨2599945622439968600247301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 55465506612052663471942421 2599945622439968600247301)
                  ·
                    refine ⟨487489804207494112546369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2599945622439968600247301 487489804207494112546369)
                    ·
                      rfl

theorem cell23_2848149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 1, 6, 4].length) (baseStart_2848149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2848149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2848149 prefixEnd_2848149 := by exact prefixLift 2848149
  have htrace : WordTrace (prefixWord ++ tailWord_2848149) baseStart_2848149 baseEnd_2848149 := by
    simpa [prefixWord, tailWord_2848149, baseEnd_2848149] using wordTrace_append hprefix tailTrace_2848149
  have hstable : (prefixWord ++ tailWord_2848149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2848149).length < 2 ^ (prefixWord ++ tailWord_2848149).sum := by decide
  have hdescent : baseEnd_2848149 < baseStart_2848149 := by decide
  rcases family_descends (prefixWord ++ tailWord_2848149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2848194 : List Nat := [3, 5, 2, 1, 1, 1, 1, 1, 1, 5, 2]
def baseStart_2848194 : Nat := 118140960795 + 2848194 * 2 ^ 59
def prefixEnd_2848194 : Nat := 4983230072969 + 3 ^ 40 * 2848194 * 2
def baseEnd_2848194 : Nat := 1462492519251934661576401

theorem tailTrace_2848194 : CollatzResearch.WordTrace tailWord_2848194 prefixEnd_2848194 1462492519251934661576401 := by
  unfold tailWord_2848194
  simp only [CollatzResearch.WordTrace]
  refine ⟨25970542360871761413353909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69254779628991363768943757 25970542360871761413353909)
  ·
    refine ⟨2434738346331727632501929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 25970542360871761413353909 2434738346331727632501929)
    ·
      refine ⟨1826053759748795724376447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2434738346331727632501929 1826053759748795724376447)
      ·
        refine ⟨2739080639623193586564671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1826053759748795724376447 2739080639623193586564671)
        ·
          refine ⟨4108620959434790379847007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2739080639623193586564671 4108620959434790379847007)
          ·
            refine ⟨6162931439152185569770511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4108620959434790379847007 6162931439152185569770511)
            ·
              refine ⟨9244397158728278354655767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6162931439152185569770511 9244397158728278354655767)
              ·
                refine ⟨13866595738092417531983651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9244397158728278354655767 13866595738092417531983651)
                ·
                  refine ⟨20799893607138626297975477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13866595738092417531983651 20799893607138626297975477)
                  ·
                    refine ⟨1949990025669246215435201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 20799893607138626297975477 1949990025669246215435201)
                    ·
                      refine ⟨1462492519251934661576401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1949990025669246215435201 1462492519251934661576401)
                      ·
                        rfl

theorem cell23_2848194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 1, 1, 1, 5, 2].length) (baseStart_2848194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2848194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2848194 prefixEnd_2848194 := by exact prefixLift 2848194
  have htrace : WordTrace (prefixWord ++ tailWord_2848194) baseStart_2848194 baseEnd_2848194 := by
    simpa [prefixWord, tailWord_2848194, baseEnd_2848194] using wordTrace_append hprefix tailTrace_2848194
  have hstable : (prefixWord ++ tailWord_2848194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2848194).length < 2 ^ (prefixWord ++ tailWord_2848194).sum := by decide
  have hdescent : baseEnd_2848194 < baseStart_2848194 := by decide
  rcases family_descends (prefixWord ++ tailWord_2848194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2848206 : List Nat := [4, 1, 1, 1, 2, 1, 4, 2, 1, 3, 3]
def baseStart_2848206 : Nat := 118140960795 + 2848206 * 2 ^ 59
def prefixEnd_2848206 : Nat := 4983230072969 + 3 ^ 40 * 2848206 * 2
def baseEnd_2848206 : Nat := 1462498681019788614626345

theorem tailTrace_2848206 : CollatzResearch.WordTrace tailWord_2848206 prefixEnd_2848206 1462498681019788614626345 := by
  unfold tailWord_2848206
  simp only [CollatzResearch.WordTrace]
  refine ⟨12985325889930446462856559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 69255071412962381135234981 12985325889930446462856559)
  ·
    refine ⟨19477988834895669694284839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12985325889930446462856559 19477988834895669694284839)
    ·
      refine ⟨29216983252343504541427259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19477988834895669694284839 29216983252343504541427259)
      ·
        refine ⟨43825474878515256812140889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29216983252343504541427259 43825474878515256812140889)
        ·
          refine ⟨32869106158886442609105667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43825474878515256812140889 32869106158886442609105667)
          ·
            refine ⟨49303659238329663913658501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32869106158886442609105667 49303659238329663913658501)
            ·
              refine ⟨9244436107186811983810969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 49303659238329663913658501 9244436107186811983810969)
              ·
                refine ⟨6933327080390108987858227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9244436107186811983810969 6933327080390108987858227)
                ·
                  refine ⟨10399990620585163481787341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6933327080390108987858227 10399990620585163481787341)
                  ·
                    refine ⟨3899996482719436305670253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10399990620585163481787341 3899996482719436305670253)
                    ·
                      refine ⟨1462498681019788614626345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3899996482719436305670253 1462498681019788614626345)
                      ·
                        rfl

theorem cell23_2848206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 4, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 4, 2, 1, 3, 3].length) (baseStart_2848206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2848206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2848206 prefixEnd_2848206 := by exact prefixLift 2848206
  have htrace : WordTrace (prefixWord ++ tailWord_2848206) baseStart_2848206 baseEnd_2848206 := by
    simpa [prefixWord, tailWord_2848206, baseEnd_2848206] using wordTrace_append hprefix tailTrace_2848206
  have hstable : (prefixWord ++ tailWord_2848206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2848206).length < 2 ^ (prefixWord ++ tailWord_2848206).sum := by decide
  have hdescent : baseEnd_2848206 < baseStart_2848206 := by decide
  rcases family_descends (prefixWord ++ tailWord_2848206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2848239 : List Nat := [1, 1, 2, 1, 4, 1, 4, 1, 2, 6]
def baseStart_2848239 : Nat := 118140960795 + 2848239 * 2 ^ 59
def prefixEnd_2848239 : Nat := 4983230072969 + 3 ^ 40 * 2848239 * 2
def baseEnd_2848239 : Nat := 487505208627128995171231

theorem tailTrace_2848239 : CollatzResearch.WordTrace tailWord_2848239 prefixEnd_2848239 487505208627128995171231 := by
  unfold tailWord_2848239
  simp only [CollatzResearch.WordTrace]
  refine ⟨103883810728324018338803771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69255873818882678892535847 103883810728324018338803771)
  ·
    refine ⟨155825716092486027508205657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103883810728324018338803771 155825716092486027508205657)
    ·
      refine ⟨116869287069364520631154243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 155825716092486027508205657 116869287069364520631154243)
      ·
        refine ⟨175303930604046780946731365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116869287069364520631154243 175303930604046780946731365)
        ·
          refine ⟨32869486988258771427512131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 175303930604046780946731365 32869486988258771427512131)
          ·
            refine ⟨49304230482388157141268197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32869486988258771427512131 49304230482388157141268197)
            ·
              refine ⟨9244543215447779463987787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 49304230482388157141268197 9244543215447779463987787)
              ·
                refine ⟨13866814823171669195981681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9244543215447779463987787 13866814823171669195981681)
                ·
                  refine ⟨10400111117378751896986261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13866814823171669195981681 10400111117378751896986261)
                  ·
                    refine ⟨487505208627128995171231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10400111117378751896986261 487505208627128995171231)
                    ·
                      rfl

theorem cell23_2848239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 4, 1, 2, 6].length) (baseStart_2848239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2848239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2848239 prefixEnd_2848239 := by exact prefixLift 2848239
  have htrace : WordTrace (prefixWord ++ tailWord_2848239) baseStart_2848239 baseEnd_2848239 := by
    simpa [prefixWord, tailWord_2848239, baseEnd_2848239] using wordTrace_append hprefix tailTrace_2848239
  have hstable : (prefixWord ++ tailWord_2848239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2848239).length < 2 ^ (prefixWord ++ tailWord_2848239).sum := by decide
  have hdescent : baseEnd_2848239 < baseStart_2848239 := by decide
  rcases family_descends (prefixWord ++ tailWord_2848239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2848240 : List Nat := [2, 1, 1, 1, 3, 5, 3, 1, 2, 1, 3]
def baseStart_2848240 : Nat := 118140960795 + 2848240 * 2 ^ 59
def prefixEnd_2848240 : Nat := 4983230072969 + 3 ^ 40 * 2848240 * 2
def baseEnd_2848240 : Nat := 1462516139362041481601189

theorem tailTrace_2848240 : CollatzResearch.WordTrace tailWord_2848240 prefixEnd_2848240 1462516139362041481601189 := by
  unfold tailWord_2848240
  simp only [CollatzResearch.WordTrace]
  refine ⟨51941923600660197754795087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69255898134213597006393449 51941923600660197754795087)
  ·
    refine ⟨77912885400990296632192631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51941923600660197754795087 77912885400990296632192631)
    ·
      refine ⟨116869328101485444948288947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77912885400990296632192631 116869328101485444948288947)
      ·
        refine ⟨175303992152228167422433421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116869328101485444948288947 175303992152228167422433421)
        ·
          refine ⟨65738997057085562783412533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 175303992152228167422433421 65738997057085562783412533)
          ·
            refine ⟨6163030974101771510944925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 65738997057085562783412533 6163030974101771510944925)
            ·
              refine ⟨2311136615288164316604347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6163030974101771510944925 2311136615288164316604347)
              ·
                refine ⟨3466704922932246474906521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2311136615288164316604347 3466704922932246474906521)
                ·
                  refine ⟨2600028692199184856179891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3466704922932246474906521 2600028692199184856179891)
                  ·
                    refine ⟨3900043038298777284269837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2600028692199184856179891 3900043038298777284269837)
                    ·
                      refine ⟨1462516139362041481601189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3900043038298777284269837 1462516139362041481601189)
                      ·
                        rfl

theorem cell23_2848240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 3, 1, 2, 1, 3].length) (baseStart_2848240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2848240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2848240 prefixEnd_2848240 := by exact prefixLift 2848240
  have htrace : WordTrace (prefixWord ++ tailWord_2848240) baseStart_2848240 baseEnd_2848240 := by
    simpa [prefixWord, tailWord_2848240, baseEnd_2848240] using wordTrace_append hprefix tailTrace_2848240
  have hstable : (prefixWord ++ tailWord_2848240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2848240).length < 2 ^ (prefixWord ++ tailWord_2848240).sum := by decide
  have hdescent : baseEnd_2848240 < baseStart_2848240 := by decide
  rcases family_descends (prefixWord ++ tailWord_2848240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2848249 : List Nat := [1, 2, 1, 3, 1, 2, 1, 4, 2, 1, 5]
def baseStart_2848249 : Nat := 118140960795 + 2848249 * 2 ^ 59
def prefixEnd_2848249 : Nat := 4983230072969 + 3 ^ 40 * 2848249 * 2
def baseEnd_2848249 : Nat := 1462520760687931946388647

theorem tailTrace_2848249 : CollatzResearch.WordTrace tailWord_2848249 prefixEnd_2848249 1462520760687931946388647 := by
  unfold tailWord_2848249
  simp only [CollatzResearch.WordTrace]
  refine ⟨103884175458287790046667801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69256116972191860031111867 103884175458287790046667801)
  ·
    refine ⟨77913131593715842535000851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103884175458287790046667801 77913131593715842535000851)
    ·
      refine ⟨116869697390573763802501277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77913131593715842535000851 116869697390573763802501277)
      ·
        refine ⟨43826136521465161425937979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 116869697390573763802501277 43826136521465161425937979)
        ·
          refine ⟨65739204782197742138906969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43826136521465161425937979 65739204782197742138906969)
          ·
            refine ⟨49304403586648306604180227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65739204782197742138906969 49304403586648306604180227)
            ·
              refine ⟨73956605379972459906270341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49304403586648306604180227 73956605379972459906270341)
              ·
                refine ⟨13866863508744836232425689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 73956605379972459906270341 13866863508744836232425689)
                ·
                  refine ⟨10400147631558627174319267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13866863508744836232425689 10400147631558627174319267)
                  ·
                    refine ⟨15600221447337940761478901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10400147631558627174319267 15600221447337940761478901)
                    ·
                      refine ⟨1462520760687931946388647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15600221447337940761478901 1462520760687931946388647)
                      ·
                        rfl

theorem cell23_2848249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 4, 2, 1, 5].length) (baseStart_2848249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2848249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2848249 prefixEnd_2848249 := by exact prefixLift 2848249
  have htrace : WordTrace (prefixWord ++ tailWord_2848249) baseStart_2848249 baseEnd_2848249 := by
    simpa [prefixWord, tailWord_2848249, baseEnd_2848249] using wordTrace_append hprefix tailTrace_2848249
  have hstable : (prefixWord ++ tailWord_2848249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2848249).length < 2 ^ (prefixWord ++ tailWord_2848249).sum := by decide
  have hdescent : baseEnd_2848249 < baseStart_2848249 := by decide
  rcases family_descends (prefixWord ++ tailWord_2848249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2848259 : List Nat := [1, 1, 1, 3, 2, 1, 2, 2, 4, 2, 4]
def baseStart_2848259 : Nat := 118140960795 + 2848259 * 2 ^ 59
def prefixEnd_2848259 : Nat := 4983230072969 + 3 ^ 40 * 2848259 * 2
def baseEnd_2848259 : Nat := 1462525895494476907263601

theorem tailTrace_2848259 : CollatzResearch.WordTrace tailWord_2848259 prefixEnd_2848259 1462525895494476907263601 := by
  unfold tailWord_2848259
  simp only [CollatzResearch.WordTrace]
  refine ⟨103884540188251561754531831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69256360125501041169687887 103884540188251561754531831)
  ·
    refine ⟨155826810282377342631797747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103884540188251561754531831 155826810282377342631797747)
    ·
      refine ⟨233740215423566013947696621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155826810282377342631797747 233740215423566013947696621)
      ·
        refine ⟨87652580783837255230386233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 233740215423566013947696621 87652580783837255230386233)
        ·
          refine ⟨65739435587877941422789675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87652580783837255230386233 65739435587877941422789675)
          ·
            refine ⟨98609153381816912134184513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65739435587877941422789675 98609153381816912134184513)
            ·
              refine ⟨73956865036362684100638385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 98609153381816912134184513 73956865036362684100638385)
              ·
                refine ⟨55467648777272013075478789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 73956865036362684100638385 55467648777272013075478789)
                ·
                  refine ⟨10400184145738502451652273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 55467648777272013075478789 10400184145738502451652273)
                  ·
                    refine ⟨7800138109303876838739205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10400184145738502451652273 7800138109303876838739205)
                    ·
                      refine ⟨1462525895494476907263601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7800138109303876838739205 1462525895494476907263601)
                      ·
                        rfl

theorem cell23_2848259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 2, 4, 2, 4].length) (baseStart_2848259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2848259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2848259 prefixEnd_2848259 := by exact prefixLift 2848259
  have htrace : WordTrace (prefixWord ++ tailWord_2848259) baseStart_2848259 baseEnd_2848259 := by
    simpa [prefixWord, tailWord_2848259, baseEnd_2848259] using wordTrace_append hprefix tailTrace_2848259
  have hstable : (prefixWord ++ tailWord_2848259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2848259).length < 2 ^ (prefixWord ++ tailWord_2848259).sum := by decide
  have hdescent : baseEnd_2848259 < baseStart_2848259 := by decide
  rcases family_descends (prefixWord ++ tailWord_2848259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2848266 : List Nat := [3, 1, 2, 2, 2, 3, 1, 1, 2, 1, 5]
def baseStart_2848266 : Nat := 118140960795 + 2848266 * 2 ^ 59
def prefixEnd_2848266 : Nat := 4983230072969 + 3 ^ 40 * 2848266 * 2
def baseEnd_2848266 : Nat := 1462529489859058379876069

theorem tailTrace_2848266 : CollatzResearch.WordTrace tailWord_2848266 prefixEnd_2848266 1462529489859058379876069 := by
  unfold tailWord_2848266
  simp only [CollatzResearch.WordTrace]
  refine ⟨25971198874806550487509163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69256530332817467966691101 25971198874806550487509163)
  ·
    refine ⟨38956798312209825731263745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25971198874806550487509163 38956798312209825731263745)
    ·
      refine ⟨29217598734157369298447809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38956798312209825731263745 29217598734157369298447809)
      ·
        refine ⟨21913199050618026973835857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29217598734157369298447809 21913199050618026973835857)
        ·
          refine ⟨16434899287963520230376893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21913199050618026973835857 16434899287963520230376893)
          ·
            refine ⟨6163087232986320086391335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16434899287963520230376893 6163087232986320086391335)
            ·
              refine ⟨9244630849479480129587003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6163087232986320086391335 9244630849479480129587003)
              ·
                refine ⟨13866946274219220194380505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9244630849479480129587003 13866946274219220194380505)
                ·
                  refine ⟨10400209705664415145785379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13866946274219220194380505 10400209705664415145785379)
                  ·
                    refine ⟨15600314558496622718678069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10400209705664415145785379 15600314558496622718678069)
                    ·
                      refine ⟨1462529489859058379876069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15600314558496622718678069 1462529489859058379876069)
                      ·
                        rfl

theorem cell23_2848266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 1, 1, 2, 1, 5].length) (baseStart_2848266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2848266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2848266 prefixEnd_2848266 := by exact prefixLift 2848266
  have htrace : WordTrace (prefixWord ++ tailWord_2848266) baseStart_2848266 baseEnd_2848266 := by
    simpa [prefixWord, tailWord_2848266, baseEnd_2848266] using wordTrace_append hprefix tailTrace_2848266
  have hstable : (prefixWord ++ tailWord_2848266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2848266).length < 2 ^ (prefixWord ++ tailWord_2848266).sum := by decide
  have hdescent : baseEnd_2848266 < baseStart_2848266 := by decide
  rcases family_descends (prefixWord ++ tailWord_2848266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2848336 : List Nat := [2, 1, 1, 1, 1, 3, 3, 4, 2, 1, 4]
def baseStart_2848336 : Nat := 118140960795 + 2848336 * 2 ^ 59
def prefixEnd_2848336 : Nat := 4983230072969 + 3 ^ 40 * 2848336 * 2
def baseEnd_2848336 : Nat := 1462565433504873106000747

theorem tailTrace_2848336 : CollatzResearch.WordTrace tailWord_2848336 prefixEnd_2848336 1462565433504873106000747 := by
  unfold tailWord_2848336
  simp only [CollatzResearch.WordTrace]
  refine ⟨51943674304486301952542431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69258232405981735936723241 51943674304486301952542431)
  ·
    refine ⟨77915511456729452928813647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51943674304486301952542431 77915511456729452928813647)
    ·
      refine ⟨116873267185094179393220471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77915511456729452928813647 116873267185094179393220471)
      ·
        refine ⟨175309900777641269089830707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116873267185094179393220471 175309900777641269089830707)
        ·
          refine ⟨262964851166461903634746061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 175309900777641269089830707 262964851166461903634746061)
          ·
            refine ⟨98611819187423213863029773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 262964851166461903634746061 98611819187423213863029773)
            ·
              refine ⟨36979432195283705198636165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 98611819187423213863029773 36979432195283705198636165)
              ·
                refine ⟨6933643536615694724744281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36979432195283705198636165 6933643536615694724744281)
                ·
                  refine ⟨5200232652461771043558211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6933643536615694724744281 5200232652461771043558211)
                  ·
                    refine ⟨7800348978692656565337317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5200232652461771043558211 7800348978692656565337317)
                    ·
                      refine ⟨1462565433504873106000747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7800348978692656565337317 1462565433504873106000747)
                      ·
                        rfl

theorem cell23_2848336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 4, 2, 1, 4].length) (baseStart_2848336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2848336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2848336 prefixEnd_2848336 := by exact prefixLift 2848336
  have htrace : WordTrace (prefixWord ++ tailWord_2848336) baseStart_2848336 baseEnd_2848336 := by
    simpa [prefixWord, tailWord_2848336, baseEnd_2848336] using wordTrace_append hprefix tailTrace_2848336
  have hstable : (prefixWord ++ tailWord_2848336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2848336).length < 2 ^ (prefixWord ++ tailWord_2848336).sum := by decide
  have hdescent : baseEnd_2848336 < baseStart_2848336 := by decide
  rcases family_descends (prefixWord ++ tailWord_2848336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2848346 : List Nat := [3, 1, 1, 2, 1, 1, 1, 2, 7, 4]
def baseStart_2848346 : Nat := 118140960795 + 2848346 * 2 ^ 59
def prefixEnd_2848346 : Nat := 4983230072969 + 3 ^ 40 * 2848346 * 2
def baseEnd_2848346 : Nat := 487523522770472688958567

theorem tailTrace_2848346 : CollatzResearch.WordTrace tailWord_2848346 prefixEnd_2848346 487523522770472688958567 := by
  unfold tailWord_2848346
  simp only [CollatzResearch.WordTrace]
  refine ⟨25971928334734093903237223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69258475559290917075299261 25971928334734093903237223)
  ·
    refine ⟨38957892502101140854855835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25971928334734093903237223 38957892502101140854855835)
    ·
      refine ⟨58436838753151711282283753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38957892502101140854855835 58436838753151711282283753)
      ·
        refine ⟨43827629064863783461712815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58436838753151711282283753 43827629064863783461712815)
        ·
          refine ⟨65741443597295675192569223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43827629064863783461712815 65741443597295675192569223)
          ·
            refine ⟨98612165395943512788853835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65741443597295675192569223 98612165395943512788853835)
            ·
              refine ⟨147918248093915269183280753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 98612165395943512788853835 147918248093915269183280753)
              ·
                refine ⟨110938686070436451887460565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 147918248093915269183280753 110938686070436451887460565)
                ·
                  refine ⟨2600125454775854341112357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 110938686070436451887460565 2600125454775854341112357)
                  ·
                    refine ⟨487523522770472688958567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2600125454775854341112357 487523522770472688958567)
                    ·
                      rfl

theorem cell23_2848346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 2, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 2, 7, 4].length) (baseStart_2848346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2848346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2848346 prefixEnd_2848346 := by exact prefixLift 2848346
  have htrace : WordTrace (prefixWord ++ tailWord_2848346) baseStart_2848346 baseEnd_2848346 := by
    simpa [prefixWord, tailWord_2848346, baseEnd_2848346] using wordTrace_append hprefix tailTrace_2848346
  have hstable : (prefixWord ++ tailWord_2848346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2848346).length < 2 ^ (prefixWord ++ tailWord_2848346).sum := by decide
  have hdescent : baseEnd_2848346 < baseStart_2848346 := by decide
  rcases family_descends (prefixWord ++ tailWord_2848346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2848353 : List Nat := [1, 2, 3, 1, 1, 3, 3, 1, 2, 4, 2]
def baseStart_2848353 : Nat := 118140960795 + 2848353 * 2 ^ 59
def prefixEnd_2848353 : Nat := 4983230072969 + 3 ^ 40 * 2848353 * 2
def baseEnd_2848353 : Nat := 1462574162675999539488169

theorem tailTrace_2848353 : CollatzResearch.WordTrace tailWord_2848353 prefixEnd_2848353 1462574162675999539488169 := by
  unfold tailWord_2848353
  simp only [CollatzResearch.WordTrace]
  refine ⟨103887968649911015808453713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69258645766607343872302475 103887968649911015808453713)
  ·
    refine ⟨77915976487433261856340285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103887968649911015808453713 77915976487433261856340285)
    ·
      refine ⟨29218491182787473196127607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 77915976487433261856340285 29218491182787473196127607)
      ·
        refine ⟨43827736774181209794191411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29218491182787473196127607 43827736774181209794191411)
        ·
          refine ⟨65741605161271814691287117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43827736774181209794191411 65741605161271814691287117)
          ·
            refine ⟨24653101935476930509232669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 65741605161271814691287117 24653101935476930509232669)
            ·
              refine ⟨9244913225803848940962251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24653101935476930509232669 9244913225803848940962251)
              ·
                refine ⟨13867369838705773411443377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9244913225803848940962251 13867369838705773411443377)
                ·
                  refine ⟨10400527379029330058582533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13867369838705773411443377 10400527379029330058582533)
                  ·
                    refine ⟨1950098883567999385984225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10400527379029330058582533 1950098883567999385984225)
                    ·
                      refine ⟨1462574162675999539488169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1950098883567999385984225 1462574162675999539488169)
                      ·
                        rfl

theorem cell23_2848353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 3, 1, 2, 4, 2].length) (baseStart_2848353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2848353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2848353 prefixEnd_2848353 := by exact prefixLift 2848353
  have htrace : WordTrace (prefixWord ++ tailWord_2848353) baseStart_2848353 baseEnd_2848353 := by
    simpa [prefixWord, tailWord_2848353, baseEnd_2848353] using wordTrace_append hprefix tailTrace_2848353
  have hstable : (prefixWord ++ tailWord_2848353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2848353).length < 2 ^ (prefixWord ++ tailWord_2848353).sum := by decide
  have hdescent : baseEnd_2848353 < baseStart_2848353 := by decide
  rcases family_descends (prefixWord ++ tailWord_2848353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2848370 : List Nat := [3, 2, 1, 2, 3, 3, 1, 1, 2, 1, 4]
def baseStart_2848370 : Nat := 118140960795 + 2848370 * 2 ^ 59
def prefixEnd_2848370 : Nat := 4983230072969 + 3 ^ 40 * 2848370 * 2
def baseEnd_2848370 : Nat := 1462582891847125972975591

theorem tailTrace_2848370 : CollatzResearch.WordTrace tailWord_2848370 prefixEnd_2848370 1462582891847125972975591 := by
  unfold tailWord_2848370
  simp only [CollatzResearch.WordTrace]
  refine ⟨25972147172712356927955641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69259059127232951807881709 25972147172712356927955641)
  ·
    refine ⟨19479110379534267695966731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25972147172712356927955641 19479110379534267695966731)
    ·
      refine ⟨29218665569301401543950097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19479110379534267695966731 29218665569301401543950097)
      ·
        refine ⟨21913999176976051157962573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29218665569301401543950097 21913999176976051157962573)
        ·
          refine ⟨8217749691366019184235965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21913999176976051157962573 8217749691366019184235965)
          ·
            refine ⟨3081656134262257194088487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8217749691366019184235965 3081656134262257194088487)
            ·
              refine ⟨4622484201393385791132731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3081656134262257194088487 4622484201393385791132731)
              ·
                refine ⟨6933726302090078686699097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4622484201393385791132731 6933726302090078686699097)
                ·
                  refine ⟨5200294726567559015024323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6933726302090078686699097 5200294726567559015024323)
                  ·
                    refine ⟨7800442089851338522536485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5200294726567559015024323 7800442089851338522536485)
                    ·
                      refine ⟨1462582891847125972975591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7800442089851338522536485 1462582891847125972975591)
                      ·
                        rfl

theorem cell23_2848370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 3, 1, 1, 2, 1, 4].length) (baseStart_2848370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2848370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2848370 prefixEnd_2848370 := by exact prefixLift 2848370
  have htrace : WordTrace (prefixWord ++ tailWord_2848370) baseStart_2848370 baseEnd_2848370 := by
    simpa [prefixWord, tailWord_2848370, baseEnd_2848370] using wordTrace_append hprefix tailTrace_2848370
  have hstable : (prefixWord ++ tailWord_2848370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2848370).length < 2 ^ (prefixWord ++ tailWord_2848370).sum := by decide
  have hdescent : baseEnd_2848370 < baseStart_2848370 := by decide
  rcases family_descends (prefixWord ++ tailWord_2848370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2848420 : List Nat := [2, 3, 1, 2, 2, 2, 2, 2, 3, 1, 3]
def baseStart_2848420 : Nat := 118140960795 + 2848420 * 2 ^ 59
def prefixEnd_2848420 : Nat := 4983230072969 + 3 ^ 40 * 2848420 * 2
def baseEnd_2848420 : Nat := 1462608565879850777350361

theorem tailTrace_2848420 : CollatzResearch.WordTrace tailWord_2848420 prefixEnd_2848420 1462608565879850777350361 := by
  unfold tailWord_2848420
  simp only [CollatzResearch.WordTrace]
  refine ⟨51945206170334143125571357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69260274893778857500761809 51945206170334143125571357)
  ·
    refine ⟨19479452313875303672089259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51945206170334143125571357 19479452313875303672089259)
    ·
      refine ⟨29219178470812955508133889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19479452313875303672089259 29219178470812955508133889)
      ·
        refine ⟨21914383853109716631100417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29219178470812955508133889 21914383853109716631100417)
        ·
          refine ⟨16435787889832287473325313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21914383853109716631100417 16435787889832287473325313)
          ·
            refine ⟨12326840917374215604993985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16435787889832287473325313 12326840917374215604993985)
            ·
              refine ⟨9245130688030661703745489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12326840917374215604993985 9245130688030661703745489)
              ·
                refine ⟨6933848016022996277809117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9245130688030661703745489 6933848016022996277809117)
                ·
                  refine ⟨2600193006008623604178419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6933848016022996277809117 2600193006008623604178419)
                  ·
                    refine ⟨3900289509012935406267629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2600193006008623604178419 3900289509012935406267629)
                    ·
                      refine ⟨1462608565879850777350361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3900289509012935406267629 1462608565879850777350361)
                      ·
                        rfl

theorem cell23_2848420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 2, 2, 3, 1, 3].length) (baseStart_2848420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2848420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2848420 prefixEnd_2848420 := by exact prefixLift 2848420
  have htrace : WordTrace (prefixWord ++ tailWord_2848420) baseStart_2848420 baseEnd_2848420 := by
    simpa [prefixWord, tailWord_2848420, baseEnd_2848420] using wordTrace_append hprefix tailTrace_2848420
  have hstable : (prefixWord ++ tailWord_2848420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2848420).length < 2 ^ (prefixWord ++ tailWord_2848420).sum := by decide
  have hdescent : baseEnd_2848420 < baseStart_2848420 := by decide
  rcases family_descends (prefixWord ++ tailWord_2848420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2848456 : List Nat := [2, 1, 3, 1, 2, 2, 1, 1, 3, 1, 6]
def baseStart_2848456 : Nat := 118140960795 + 2848456 * 2 ^ 59
def prefixEnd_2848456 : Nat := 4983230072969 + 3 ^ 40 * 2848456 * 2
def baseEnd_2848456 : Nat := 1462627051183412636500195

theorem tailTrace_2848456 : CollatzResearch.WordTrace tailWord_2848456 prefixEnd_2848456 1462627051183412636500195 := by
  unfold tailWord_2848456
  simp only [CollatzResearch.WordTrace]
  refine ⟨51945862684268932199726611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69261150245691909599635481 51945862684268932199726611)
  ·
    refine ⟨77918794026403398299589917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51945862684268932199726611 77918794026403398299589917)
    ·
      refine ⟨29219547759901274362346219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 77918794026403398299589917 29219547759901274362346219)
      ·
        refine ⟨43829321639851911543519329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29219547759901274362346219 43829321639851911543519329)
        ·
          refine ⟨32871991229888933657639497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43829321639851911543519329 32871991229888933657639497)
          ·
            refine ⟨24653993422416700243229623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32871991229888933657639497 24653993422416700243229623)
            ·
              refine ⟨36980990133625050364844435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24653993422416700243229623 36980990133625050364844435)
              ·
                refine ⟨55471485200437575547266653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36980990133625050364844435 55471485200437575547266653)
                ·
                  refine ⟨20801806950164090830224995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 55471485200437575547266653 20801806950164090830224995)
                  ·
                    refine ⟨31202710425246136245337493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20801806950164090830224995 31202710425246136245337493)
                    ·
                      refine ⟨1462627051183412636500195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 31202710425246136245337493 1462627051183412636500195)
                      ·
                        rfl

theorem cell23_2848456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 1, 3, 1, 6].length) (baseStart_2848456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2848456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2848456 prefixEnd_2848456 := by exact prefixLift 2848456
  have htrace : WordTrace (prefixWord ++ tailWord_2848456) baseStart_2848456 baseEnd_2848456 := by
    simpa [prefixWord, tailWord_2848456, baseEnd_2848456] using wordTrace_append hprefix tailTrace_2848456
  have hstable : (prefixWord ++ tailWord_2848456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2848456).length < 2 ^ (prefixWord ++ tailWord_2848456).sum := by decide
  have hdescent : baseEnd_2848456 < baseStart_2848456 := by decide
  rcases family_descends (prefixWord ++ tailWord_2848456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2848477 : List Nat := [1, 4, 3, 3, 1, 1, 1, 1, 3, 1, 4]
def baseStart_2848477 : Nat := 118140960795 + 2848477 * 2 ^ 59
def prefixEnd_2848477 : Nat := 4983230072969 + 3 ^ 40 * 2848477 * 2
def baseEnd_2848477 : Nat := 1462637834277157054337599

theorem tailTrace_2848477 : CollatzResearch.WordTrace tailWord_2848477 prefixEnd_2848477 1462637834277157054337599 := by
  unfold tailWord_2848477
  simp only [CollatzResearch.WordTrace]
  refine ⟨103892491301461784985967685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69261660867641189990645123 103892491301461784985967685)
  ·
    refine ⟨19479842119024084684868941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 103892491301461784985967685 19479842119024084684868941)
    ·
      refine ⟨7304940794634031756825853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19479842119024084684868941 7304940794634031756825853)
      ·
        refine ⟨2739352797987761908809695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7304940794634031756825853 2739352797987761908809695)
        ·
          refine ⟨4109029196981642863214543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2739352797987761908809695 4109029196981642863214543)
          ·
            refine ⟨6163543795472464294821815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4109029196981642863214543 6163543795472464294821815)
            ·
              refine ⟨9245315693208696442232723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6163543795472464294821815 9245315693208696442232723)
              ·
                refine ⟨13867973539813044663349085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9245315693208696442232723 13867973539813044663349085)
                ·
                  refine ⟨5200490077429891748755907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13867973539813044663349085 5200490077429891748755907)
                  ·
                    refine ⟨7800735116144837623133861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5200490077429891748755907 7800735116144837623133861)
                    ·
                      refine ⟨1462637834277157054337599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7800735116144837623133861 1462637834277157054337599)
                      ·
                        rfl

theorem cell23_2848477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 1, 1, 3, 1, 4].length) (baseStart_2848477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2848477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2848477 prefixEnd_2848477 := by exact prefixLift 2848477
  have htrace : WordTrace (prefixWord ++ tailWord_2848477) baseStart_2848477 baseEnd_2848477 := by
    simpa [prefixWord, tailWord_2848477, baseEnd_2848477] using wordTrace_append hprefix tailTrace_2848477
  have hstable : (prefixWord ++ tailWord_2848477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2848477).length < 2 ^ (prefixWord ++ tailWord_2848477).sum := by decide
  have hdescent : baseEnd_2848477 < baseStart_2848477 := by decide
  rcases family_descends (prefixWord ++ tailWord_2848477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2848480 : List Nat := [2, 1, 1, 3, 1, 2, 5, 2, 1, 2, 3]
def baseStart_2848480 : Nat := 118140960795 + 2848480 * 2 ^ 59
def prefixEnd_2848480 : Nat := 4983230072969 + 3 ^ 40 * 2848480 * 2
def baseEnd_2848480 : Nat := 1462639374719120542600085

theorem tailTrace_2848480 : CollatzResearch.WordTrace tailWord_2848480 prefixEnd_2848480 1462639374719120542600085 := by
  unfold tailWord_2848480
  simp only [CollatzResearch.WordTrace]
  refine ⟨51946300360225458249163447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69261733813633944332217929 51946300360225458249163447)
  ·
    refine ⟨77919450540338187373745171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51946300360225458249163447 77919450540338187373745171)
    ·
      refine ⟨116879175810507281060617757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77919450540338187373745171 116879175810507281060617757)
      ·
        refine ⟨43829690928940230397731659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 116879175810507281060617757 43829690928940230397731659)
        ·
          refine ⟨65744536393410345596597489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43829690928940230397731659 65744536393410345596597489)
          ·
            refine ⟨49308402295057759197448117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65744536393410345596597489 49308402295057759197448117)
            ·
              refine ⟨4622662715161664924760761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 49308402295057759197448117 4622662715161664924760761)
              ·
                refine ⟨3466997036371248693570571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4622662715161664924760761 3466997036371248693570571)
                ·
                  refine ⟨5200495554556873040355857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3466997036371248693570571 5200495554556873040355857)
                  ·
                    refine ⟨3900371665917654780266893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5200495554556873040355857 3900371665917654780266893)
                    ·
                      refine ⟨1462639374719120542600085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3900371665917654780266893 1462639374719120542600085)
                      ·
                        rfl

theorem cell23_2848480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 5, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 5, 2, 1, 2, 3].length) (baseStart_2848480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2848480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2848480 prefixEnd_2848480 := by exact prefixLift 2848480
  have htrace : WordTrace (prefixWord ++ tailWord_2848480) baseStart_2848480 baseEnd_2848480 := by
    simpa [prefixWord, tailWord_2848480, baseEnd_2848480] using wordTrace_append hprefix tailTrace_2848480
  have hstable : (prefixWord ++ tailWord_2848480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2848480).length < 2 ^ (prefixWord ++ tailWord_2848480).sum := by decide
  have hdescent : baseEnd_2848480 < baseStart_2848480 := by decide
  rcases family_descends (prefixWord ++ tailWord_2848480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2848494 : List Nat := [4, 1, 2, 1, 1, 2, 2, 5, 1, 2, 2]
def baseStart_2848494 : Nat := 118140960795 + 2848494 * 2 ^ 59
def prefixEnd_2848494 : Nat := 4983230072969 + 3 ^ 40 * 2848494 * 2
def baseEnd_2848494 : Nat := 1462646563448283487825021

theorem tailTrace_2848494 : CollatzResearch.WordTrace tailWord_2848494 prefixEnd_2848494 1462646563448283487825021 := by
  unfold tailWord_2848494
  simp only [CollatzResearch.WordTrace]
  refine ⟨12986638917800024611167067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 69262074228266797926224357 12986638917800024611167067)
  ·
    refine ⟨19479958376700036916750601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12986638917800024611167067 19479958376700036916750601)
    ·
      refine ⟨14609968782525027687562951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19479958376700036916750601 14609968782525027687562951)
      ·
        refine ⟨21914953173787541531344427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14609968782525027687562951 21914953173787541531344427)
        ·
          refine ⟨32872429760681312297016641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21914953173787541531344427 32872429760681312297016641)
          ·
            refine ⟨24654322320510984222762481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32872429760681312297016641 24654322320510984222762481)
            ·
              refine ⟨18490741740383238167071861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24654322320510984222762481 18490741740383238167071861)
              ·
                refine ⟨1733507038160928578162987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 18490741740383238167071861 1733507038160928578162987)
                ·
                  refine ⟨2600260557241392867244481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1733507038160928578162987 2600260557241392867244481)
                  ·
                    refine ⟨1950195417931044650433361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2600260557241392867244481 1950195417931044650433361)
                    ·
                      refine ⟨1462646563448283487825021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1950195417931044650433361 1462646563448283487825021)
                      ·
                        rfl

theorem cell23_2848494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 2, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 2, 5, 1, 2, 2].length) (baseStart_2848494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2848494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2848494 prefixEnd_2848494 := by exact prefixLift 2848494
  have htrace : WordTrace (prefixWord ++ tailWord_2848494) baseStart_2848494 baseEnd_2848494 := by
    simpa [prefixWord, tailWord_2848494, baseEnd_2848494] using wordTrace_append hprefix tailTrace_2848494
  have hstable : (prefixWord ++ tailWord_2848494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2848494).length < 2 ^ (prefixWord ++ tailWord_2848494).sum := by decide
  have hdescent : baseEnd_2848494 < baseStart_2848494 := by decide
  rcases family_descends (prefixWord ++ tailWord_2848494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2848497 : List Nat := [1, 2, 2, 2, 2, 4, 3, 1, 1, 2, 3]
def baseStart_2848497 : Nat := 118140960795 + 2848497 * 2 ^ 59
def prefixEnd_2848497 : Nat := 4983230072969 + 3 ^ 40 * 2848497 * 2
def baseEnd_2848497 : Nat := 1462648103890246976087507

theorem tailTrace_2848497 : CollatzResearch.WordTrace tailWord_2848497 prefixEnd_2848497 1462648103890246976087507 := by
  unfold tailWord_2848497
  simp only [CollatzResearch.WordTrace]
  refine ⟨103893220761389328401695745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69262147174259552267797163 103893220761389328401695745)
  ·
    refine ⟨77919915571041996301271809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103893220761389328401695745 77919915571041996301271809)
    ·
      refine ⟨58439936678281497225953857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77919915571041996301271809 58439936678281497225953857)
      ·
        refine ⟨43829952508711122919465393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58439936678281497225953857 43829952508711122919465393)
        ·
          refine ⟨32872464381533342189599045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43829952508711122919465393 32872464381533342189599045)
          ·
            refine ⟨6163587071537501660549821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32872464381533342189599045 6163587071537501660549821)
            ·
              refine ⟨2311345151826563122706183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6163587071537501660549821 2311345151826563122706183)
              ·
                refine ⟨3467017727739844684059275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2311345151826563122706183 3467017727739844684059275)
                ·
                  refine ⟨5200526591609767026088913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3467017727739844684059275 5200526591609767026088913)
                  ·
                    refine ⟨3900394943707325269566685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5200526591609767026088913 3900394943707325269566685)
                    ·
                      refine ⟨1462648103890246976087507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3900394943707325269566685 1462648103890246976087507)
                      ·
                        rfl

theorem cell23_2848497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 3, 1, 1, 2, 3].length) (baseStart_2848497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2848497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2848497 prefixEnd_2848497 := by exact prefixLift 2848497
  have htrace : WordTrace (prefixWord ++ tailWord_2848497) baseStart_2848497 baseEnd_2848497 := by
    simpa [prefixWord, tailWord_2848497, baseEnd_2848497] using wordTrace_append hprefix tailTrace_2848497
  have hstable : (prefixWord ++ tailWord_2848497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2848497).length < 2 ^ (prefixWord ++ tailWord_2848497).sum := by decide
  have hdescent : baseEnd_2848497 < baseStart_2848497 := by decide
  rcases family_descends (prefixWord ++ tailWord_2848497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2848500 : List Nat := [2, 6, 1, 1, 1, 12]
def baseStart_2848500 : Nat := 118140960795 + 2848500 * 2 ^ 59
def prefixEnd_2848500 : Nat := 4983230072969 + 3 ^ 40 * 2848500 * 2
def baseEnd_2848500 : Nat := 6019134338815680923251

theorem tailTrace_2848500 : CollatzResearch.WordTrace tailWord_2848500 prefixEnd_2848500 6019134338815680923251 := by
  unfold tailWord_2848500
  simp only [CollatzResearch.WordTrace]
  refine ⟨51946665090189229957027477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69262220120252306609369969 51946665090189229957027477)
  ·
    refine ⟨2434999926102620154235663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 51946665090189229957027477 2434999926102620154235663)
    ·
      refine ⟨3652499889153930231353495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2434999926102620154235663 3652499889153930231353495)
      ·
        refine ⟨5478749833730895347030243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3652499889153930231353495 5478749833730895347030243)
        ·
          refine ⟨8218124750596343020545365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5478749833730895347030243 8218124750596343020545365)
          ·
            refine ⟨6019134338815680923251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 8218124750596343020545365 6019134338815680923251)
            ·
              rfl

theorem cell23_2848500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 12].length) (baseStart_2848500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2848500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2848500 prefixEnd_2848500 := by exact prefixLift 2848500
  have htrace : WordTrace (prefixWord ++ tailWord_2848500) baseStart_2848500 baseEnd_2848500 := by
    simpa [prefixWord, tailWord_2848500, baseEnd_2848500] using wordTrace_append hprefix tailTrace_2848500
  have hstable : (prefixWord ++ tailWord_2848500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2848500).length < 2 ^ (prefixWord ++ tailWord_2848500).sum := by decide
  have hdescent : baseEnd_2848500 < baseStart_2848500 := by decide
  rcases family_descends (prefixWord ++ tailWord_2848500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2848520 : List Nat := [2, 1, 3, 2, 2, 1, 1, 1, 5, 3, 2]
def baseStart_2848520 : Nat := 118140960795 + 2848520 * 2 ^ 59
def prefixEnd_2848520 : Nat := 4983230072969 + 3 ^ 40 * 2848520 * 2
def baseEnd_2848520 : Nat := 1462659913945300386099901

theorem tailTrace_2848520 : CollatzResearch.WordTrace tailWord_2848520 prefixEnd_2848520 1462659913945300386099901 := by
  unfold tailWord_2848520
  simp only [CollatzResearch.WordTrace]
  refine ⟨51947029820153001664891507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69262706426870668886522009 51947029820153001664891507)
  ·
    refine ⟨77920544730229502497337261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51947029820153001664891507 77920544730229502497337261)
    ·
      refine ⟨29220204273836063436501473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 77920544730229502497337261 29220204273836063436501473)
      ·
        refine ⟨21915153205377047577376105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29220204273836063436501473 21915153205377047577376105)
        ·
          refine ⟨16436364904032785683032079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21915153205377047577376105 16436364904032785683032079)
          ·
            refine ⟨24654547356049178524548119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16436364904032785683032079 24654547356049178524548119)
            ·
              refine ⟨36981821034073767786822179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24654547356049178524548119 36981821034073767786822179)
              ·
                refine ⟨55472731551110651680233269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36981821034073767786822179 55472731551110651680233269)
                ·
                  refine ⟨5200568582916623595021869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 55472731551110651680233269 5200568582916623595021869)
                  ·
                    refine ⟨1950213218593733848133201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5200568582916623595021869 1950213218593733848133201)
                    ·
                      refine ⟨1462659913945300386099901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1950213218593733848133201 1462659913945300386099901)
                      ·
                        rfl

theorem cell23_2848520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 1, 5, 3, 2].length) (baseStart_2848520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2848520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2848520 prefixEnd_2848520 := by exact prefixLift 2848520
  have htrace : WordTrace (prefixWord ++ tailWord_2848520) baseStart_2848520 baseEnd_2848520 := by
    simpa [prefixWord, tailWord_2848520, baseEnd_2848520] using wordTrace_append hprefix tailTrace_2848520
  have hstable : (prefixWord ++ tailWord_2848520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2848520).length < 2 ^ (prefixWord ++ tailWord_2848520).sum := by decide
  have hdescent : baseEnd_2848520 < baseStart_2848520 := by decide
  rcases family_descends (prefixWord ++ tailWord_2848520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2848567 : List Nat := [1, 1, 3, 1, 2, 1, 2, 6, 2, 2, 2]
def baseStart_2848567 : Nat := 118140960795 + 2848567 * 2 ^ 59
def prefixEnd_2848567 : Nat := 4983230072969 + 3 ^ 40 * 2848567 * 2
def baseEnd_2848567 : Nat := 1462684047536061702212185

theorem tailTrace_2848567 : CollatzResearch.WordTrace tailWord_2848567 prefixEnd_2848567 1462684047536061702212185 := by
  unfold tailWord_2848567
  simp only [CollatzResearch.WordTrace]
  refine ⟨103895773871135730356743955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69263849247423820237829303 103895773871135730356743955)
  ·
    refine ⟨155843660806703595535115933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103895773871135730356743955 155843660806703595535115933)
    ·
      refine ⟨58441372802513848325668475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 155843660806703595535115933 58441372802513848325668475)
      ·
        refine ⟨87662059203770772488502713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58441372802513848325668475 87662059203770772488502713)
        ·
          refine ⟨65746544402828079366377035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87662059203770772488502713 65746544402828079366377035)
          ·
            refine ⟨98619816604242119049565553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65746544402828079366377035 98619816604242119049565553)
            ·
              refine ⟨73964862453181589287174165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 98619816604242119049565553 73964862453181589287174165)
              ·
                refine ⟨3467102927492886997836289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 73964862453181589287174165 3467102927492886997836289)
                ·
                  refine ⟨2600327195619665248377217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3467102927492886997836289 2600327195619665248377217)
                  ·
                    refine ⟨1950245396714748936282913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2600327195619665248377217 1950245396714748936282913)
                    ·
                      refine ⟨1462684047536061702212185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1950245396714748936282913 1462684047536061702212185)
                      ·
                        rfl

theorem cell23_2848567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 6, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 6, 2, 2, 2].length) (baseStart_2848567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2848567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2848567 prefixEnd_2848567 := by exact prefixLift 2848567
  have htrace : WordTrace (prefixWord ++ tailWord_2848567) baseStart_2848567 baseEnd_2848567 := by
    simpa [prefixWord, tailWord_2848567, baseEnd_2848567] using wordTrace_append hprefix tailTrace_2848567
  have hstable : (prefixWord ++ tailWord_2848567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2848567).length < 2 ^ (prefixWord ++ tailWord_2848567).sum := by decide
  have hdescent : baseEnd_2848567 < baseStart_2848567 := by decide
  rcases family_descends (prefixWord ++ tailWord_2848567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2848607 : List Nat := [1, 1, 2, 3, 1, 6, 1, 3, 5]
def baseStart_2848607 : Nat := 118140960795 + 2848607 * 2 ^ 59
def prefixEnd_2848607 : Nat := 4983230072969 + 3 ^ 40 * 2848607 * 2
def baseEnd_2848607 : Nat := 162522731862471282856889

theorem tailTrace_2848607 : CollatzResearch.WordTrace tailWord_2848607 prefixEnd_2848607 162522731862471282856889 := by
  unfold tailWord_2848607
  simp only [CollatzResearch.WordTrace]
  refine ⟨103897232790990817188200075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69264821860660544792133383 103897232790990817188200075)
  ·
    refine ⟨155845849186486225782300113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103897232790990817188200075 155845849186486225782300113)
    ·
      refine ⟨116884386889864669336725085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 155845849186486225782300113 116884386889864669336725085)
      ·
        refine ⟨43831645083699251001271907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 116884386889864669336725085 43831645083699251001271907)
        ·
          refine ⟨65747467625548876501907861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43831645083699251001271907 65747467625548876501907861)
          ·
            refine ⟨3081912544947603586026931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 65747467625548876501907861 3081912544947603586026931)
            ·
              refine ⟨4622868817421405379040397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3081912544947603586026931 4622868817421405379040397)
              ·
                refine ⟨1733575806533027017140149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4622868817421405379040397 1733575806533027017140149)
                ·
                  refine ⟨162522731862471282856889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1733575806533027017140149 162522731862471282856889)
                  ·
                    rfl

theorem cell23_2848607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 6, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 6, 1, 3, 5].length) (baseStart_2848607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2848607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2848607 prefixEnd_2848607 := by exact prefixLift 2848607
  have htrace : WordTrace (prefixWord ++ tailWord_2848607) baseStart_2848607 baseEnd_2848607 := by
    simpa [prefixWord, tailWord_2848607, baseEnd_2848607] using wordTrace_append hprefix tailTrace_2848607
  have hstable : (prefixWord ++ tailWord_2848607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2848607).length < 2 ^ (prefixWord ++ tailWord_2848607).sum := by decide
  have hdescent : baseEnd_2848607 < baseStart_2848607 := by decide
  rcases family_descends (prefixWord ++ tailWord_2848607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2848613 : List Nat := [1, 3, 1, 3, 1, 1, 1, 4, 1, 2, 5]
def baseStart_2848613 : Nat := 118140960795 + 2848613 * 2 ^ 59
def prefixEnd_2848613 : Nat := 4983230072969 + 3 ^ 40 * 2848613 * 2
def baseEnd_2848613 : Nat := 1462707667646168522236973

theorem tailTrace_2848613 : CollatzResearch.WordTrace tailWord_2848613 prefixEnd_2848613 1462707667646168522236973 := by
  unfold tailWord_2848613
  simp only [CollatzResearch.WordTrace]
  refine ⟨103897451628969080212918493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69264967752646053475278995 103897451628969080212918493)
  ·
    refine ⟨38961544360863405079844435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 103897451628969080212918493 38961544360863405079844435)
    ·
      refine ⟨58442316541295107619766653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38961544360863405079844435 58442316541295107619766653)
      ·
        refine ⟨21915868702985665357412495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58442316541295107619766653 21915868702985665357412495)
        ·
          refine ⟨32873803054478498036118743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21915868702985665357412495 32873803054478498036118743)
          ·
            refine ⟨49310704581717747054178115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32873803054478498036118743 49310704581717747054178115)
            ·
              refine ⟨73966056872576620581267173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49310704581717747054178115 73966056872576620581267173)
              ·
                refine ⟨13868635663608116358987595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 73966056872576620581267173 13868635663608116358987595)
                ·
                  refine ⟨20802953495412174538481393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13868635663608116358987595 20802953495412174538481393)
                  ·
                    refine ⟨15602215121559130903861045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20802953495412174538481393 15602215121559130903861045)
                    ·
                      refine ⟨1462707667646168522236973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15602215121559130903861045 1462707667646168522236973)
                      ·
                        rfl

theorem cell23_2848613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 4, 1, 2, 5].length) (baseStart_2848613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2848613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2848613 prefixEnd_2848613 := by exact prefixLift 2848613
  have htrace : WordTrace (prefixWord ++ tailWord_2848613) baseStart_2848613 baseEnd_2848613 := by
    simpa [prefixWord, tailWord_2848613, baseEnd_2848613] using wordTrace_append hprefix tailTrace_2848613
  have hstable : (prefixWord ++ tailWord_2848613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2848613).length < 2 ^ (prefixWord ++ tailWord_2848613).sum := by decide
  have hdescent : baseEnd_2848613 < baseStart_2848613 := by decide
  rcases family_descends (prefixWord ++ tailWord_2848613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2848620 : List Nat := [2, 2, 1, 1, 4, 3, 1, 2, 2, 5]
def baseStart_2848620 : Nat := 118140960795 + 2848620 * 2 ^ 59
def prefixEnd_2848620 : Nat := 4983230072969 + 3 ^ 40 * 2848620 * 2
def baseEnd_2848620 : Nat := 487570420670249998283147

theorem tailTrace_2848620 : CollatzResearch.WordTrace tailWord_2848620 prefixEnd_2848620 487570420670249998283147 := by
  unfold tailWord_2848620
  simp only [CollatzResearch.WordTrace]
  refine ⟨51948853469971860204211657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69265137959962480272282209 51948853469971860204211657)
  ·
    refine ⟨38961640102478895153158743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51948853469971860204211657 38961640102478895153158743)
    ·
      refine ⟨58442460153718342729738115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38961640102478895153158743 58442460153718342729738115)
      ·
        refine ⟨87663690230577514094607173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58442460153718342729738115 87663690230577514094607173)
        ·
          refine ⟨16436941918233283892738845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 87663690230577514094607173 16436941918233283892738845)
          ·
            refine ⟨6163853219337481459777067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16436941918233283892738845 6163853219337481459777067)
            ·
              refine ⟨9245779829006222189665601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6163853219337481459777067 9245779829006222189665601)
              ·
                refine ⟨6934334871754666642249201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9245779829006222189665601 6934334871754666642249201)
                ·
                  refine ⟨5200751153815999981686901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6934334871754666642249201 5200751153815999981686901)
                  ·
                    refine ⟨487570420670249998283147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5200751153815999981686901 487570420670249998283147)
                    ·
                      rfl

theorem cell23_2848620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 5].length) (baseStart_2848620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2848620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2848620 prefixEnd_2848620 := by exact prefixLift 2848620
  have htrace : WordTrace (prefixWord ++ tailWord_2848620) baseStart_2848620 baseEnd_2848620 := by
    simpa [prefixWord, tailWord_2848620, baseEnd_2848620] using wordTrace_append hprefix tailTrace_2848620
  have hstable : (prefixWord ++ tailWord_2848620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2848620).length < 2 ^ (prefixWord ++ tailWord_2848620).sum := by decide
  have hdescent : baseEnd_2848620 < baseStart_2848620 := by decide
  rcases family_descends (prefixWord ++ tailWord_2848620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2848640 : List Nat := [2, 1, 1, 2, 1, 2, 4, 1, 1, 6, 2]
def baseStart_2848640 : Nat := 118140960795 + 2848640 * 2 ^ 59
def prefixEnd_2848640 : Nat := 4983230072969 + 3 ^ 40 * 2848640 * 2
def baseEnd_2848640 : Nat := 1462721531623839916599349

theorem tailTrace_2848640 : CollatzResearch.WordTrace tailWord_2848640 prefixEnd_2848640 1462721531623839916599349 := by
  unfold tailWord_2848640
  simp only [CollatzResearch.WordTrace]
  refine ⟨51949218199935631912075687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69265624266580842549434249 51949218199935631912075687)
  ·
    refine ⟨77923827299903447868113531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51949218199935631912075687 77923827299903447868113531)
    ·
      refine ⟨116885740949855171802170297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77923827299903447868113531 116885740949855171802170297)
      ·
        refine ⟨87664305712391378851627723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 116885740949855171802170297 87664305712391378851627723)
        ·
          refine ⟨131496458568587068277441585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87664305712391378851627723 131496458568587068277441585)
          ·
            refine ⟨98622343926440301208081189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 131496458568587068277441585 98622343926440301208081189)
            ·
              refine ⟨18491689486207556476515223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 98622343926440301208081189 18491689486207556476515223)
              ·
                refine ⟨27737534229311334714772835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18491689486207556476515223 27737534229311334714772835)
                ·
                  refine ⟨41606301343967002072159253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27737534229311334714772835 41606301343967002072159253)
                  ·
                    refine ⟨1950295375498453222132465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 41606301343967002072159253 1950295375498453222132465)
                    ·
                      refine ⟨1462721531623839916599349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1950295375498453222132465 1462721531623839916599349)
                      ·
                        rfl

theorem cell23_2848640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 4, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 4, 1, 1, 6, 2].length) (baseStart_2848640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2848640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2848640 prefixEnd_2848640 := by exact prefixLift 2848640
  have htrace : WordTrace (prefixWord ++ tailWord_2848640) baseStart_2848640 baseEnd_2848640 := by
    simpa [prefixWord, tailWord_2848640, baseEnd_2848640] using wordTrace_append hprefix tailTrace_2848640
  have hstable : (prefixWord ++ tailWord_2848640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2848640).length < 2 ^ (prefixWord ++ tailWord_2848640).sum := by decide
  have hdescent : baseEnd_2848640 < baseStart_2848640 := by decide
  rcases family_descends (prefixWord ++ tailWord_2848640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2848654 : List Nat := [4, 1, 1, 5, 1, 1, 2, 1, 2, 5]
def baseStart_2848654 : Nat := 118140960795 + 2848654 * 2 ^ 59
def prefixEnd_2848654 : Nat := 4983230072969 + 3 ^ 40 * 2848654 * 2
def baseEnd_2848654 : Nat := 487576240117667620608095

theorem tailTrace_2848654 : CollatzResearch.WordTrace tailWord_2848654 prefixEnd_2848654 487576240117667620608095 := by
  unfold tailWord_2848654
  simp only [CollatzResearch.WordTrace]
  refine ⟨12987368377727568026895127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 69265964681213696143440677 12987368377727568026895127)
  ·
    refine ⟨19481052566591352040342691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12987368377727568026895127 19481052566591352040342691)
    ·
      refine ⟨29221578849887028060514037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19481052566591352040342691 29221578849887028060514037)
      ·
        refine ⟨2739523017176908880673191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 29221578849887028060514037 2739523017176908880673191)
        ·
          refine ⟨4109284525765363321009787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2739523017176908880673191 4109284525765363321009787)
          ·
            refine ⟨6163926788648044981514681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4109284525765363321009787 6163926788648044981514681)
            ·
              refine ⟨4622945091486033736136011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6163926788648044981514681 4622945091486033736136011)
              ·
                refine ⟨6934417637229050604204017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4622945091486033736136011 6934417637229050604204017)
                ·
                  refine ⟨5200813227921787953153013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6934417637229050604204017 5200813227921787953153013)
                  ·
                    refine ⟨487576240117667620608095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5200813227921787953153013 487576240117667620608095)
                    ·
                      rfl

theorem cell23_2848654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 2, 1, 2, 5].length) (baseStart_2848654 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2848654 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2848654 prefixEnd_2848654 := by exact prefixLift 2848654
  have htrace : WordTrace (prefixWord ++ tailWord_2848654) baseStart_2848654 baseEnd_2848654 := by
    simpa [prefixWord, tailWord_2848654, baseEnd_2848654] using wordTrace_append hprefix tailTrace_2848654
  have hstable : (prefixWord ++ tailWord_2848654).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2848654).length < 2 ^ (prefixWord ++ tailWord_2848654).sum := by decide
  have hdescent : baseEnd_2848654 < baseStart_2848654 := by decide
  rcases family_descends (prefixWord ++ tailWord_2848654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2848703 : List Nat := [1, 1, 2, 2, 2, 1, 3, 1, 2, 1, 7]
def baseStart_2848703 : Nat := 118140960795 + 2848703 * 2 ^ 59
def prefixEnd_2848703 : Nat := 4983230072969 + 3 ^ 40 * 2848703 * 2
def baseEnd_2848703 : Nat := 1462753880905073170111559

theorem tailTrace_2848703 : CollatzResearch.WordTrace tailWord_2848703 prefixEnd_2848703 1462753880905073170111559 := by
  unfold tailWord_2848703
  simp only [CollatzResearch.WordTrace]
  refine ⟨103900734198643025583694763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69267156132428683722463175 103900734198643025583694763)
  ·
    refine ⟨155851101297964538375542145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103900734198643025583694763 155851101297964538375542145)
    ·
      refine ⟨116888325973473403781656609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 155851101297964538375542145 116888325973473403781656609)
      ·
        refine ⟨87666244480105052836242457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 116888325973473403781656609 87666244480105052836242457)
        ·
          refine ⟨65749683360078789627181843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87666244480105052836242457 65749683360078789627181843)
          ·
            refine ⟨98624525040118184440772765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65749683360078789627181843 98624525040118184440772765)
            ·
              refine ⟨36984196890044319165289787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 98624525040118184440772765 36984196890044319165289787)
              ·
                refine ⟨55476295335066478747934681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36984196890044319165289787 55476295335066478747934681)
                ·
                  refine ⟨41607221501299859060951011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 55476295335066478747934681 41607221501299859060951011)
                  ·
                    refine ⟨62410832251949788591426517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 41607221501299859060951011 62410832251949788591426517)
                    ·
                      refine ⟨1462753880905073170111559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 62410832251949788591426517 1462753880905073170111559)
                      ·
                        rfl

theorem cell23_2848703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 1, 2, 1, 7].length) (baseStart_2848703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2848703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2848703 prefixEnd_2848703 := by exact prefixLift 2848703
  have htrace : WordTrace (prefixWord ++ tailWord_2848703) baseStart_2848703 baseEnd_2848703 := by
    simpa [prefixWord, tailWord_2848703, baseEnd_2848703] using wordTrace_append hprefix tailTrace_2848703
  have hstable : (prefixWord ++ tailWord_2848703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2848703).length < 2 ^ (prefixWord ++ tailWord_2848703).sum := by decide
  have hdescent : baseEnd_2848703 < baseStart_2848703 := by decide
  rcases family_descends (prefixWord ++ tailWord_2848703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2848764 : List Nat := [2, 2, 2, 1, 2, 2, 1, 4, 3, 2, 2]
def baseStart_2848764 : Nat := 118140960795 + 2848764 * 2 ^ 59
def prefixEnd_2848764 : Nat := 4983230072969 + 3 ^ 40 * 2848764 * 2
def baseEnd_2848764 : Nat := 1462785203224997431448779

theorem tailTrace_2848764 : CollatzResearch.WordTrace tailWord_2848764 prefixEnd_2848764 1462785203224997431448779 := by
  unfold tailWord_2848764
  simp only [CollatzResearch.WordTrace]
  refine ⟨51951479525711016500832673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69268639367614688667776897 51951479525711016500832673)
  ·
    refine ⟨38963609644283262375624505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51951479525711016500832673 38963609644283262375624505)
    ·
      refine ⟨29222707233212446781718379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38963609644283262375624505 29222707233212446781718379)
      ·
        refine ⟨43834060849818670172577569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29222707233212446781718379 43834060849818670172577569)
        ·
          refine ⟨32875545637364002629433177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43834060849818670172577569 32875545637364002629433177)
          ·
            refine ⟨24656659228023001972074883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32875545637364002629433177 24656659228023001972074883)
            ·
              refine ⟨36984988842034502958112325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24656659228023001972074883 36984988842034502958112325)
              ·
                refine ⟨6934685407881469304646061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36984988842034502958112325 6934685407881469304646061)
                ·
                  refine ⟨2600507027955550989242273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6934685407881469304646061 2600507027955550989242273)
                  ·
                    refine ⟨1950380270966663241931705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2600507027955550989242273 1950380270966663241931705)
                    ·
                      refine ⟨1462785203224997431448779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1950380270966663241931705 1462785203224997431448779)
                      ·
                        rfl

theorem cell23_2848764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 4, 3, 2, 2].length) (baseStart_2848764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2848764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2848764 prefixEnd_2848764 := by exact prefixLift 2848764
  have htrace : WordTrace (prefixWord ++ tailWord_2848764) baseStart_2848764 baseEnd_2848764 := by
    simpa [prefixWord, tailWord_2848764, baseEnd_2848764] using wordTrace_append hprefix tailTrace_2848764
  have hstable : (prefixWord ++ tailWord_2848764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2848764).length < 2 ^ (prefixWord ++ tailWord_2848764).sum := by decide
  have hdescent : baseEnd_2848764 < baseStart_2848764 := by decide
  rcases family_descends (prefixWord ++ tailWord_2848764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2848840 : List Nat := [2, 1, 3, 1, 1, 1, 2, 3, 1, 3, 5]
def baseStart_2848840 : Nat := 118140960795 + 2848840 * 2 ^ 59
def prefixEnd_2848840 : Nat := 4983230072969 + 3 ^ 40 * 2848840 * 2
def baseEnd_2848840 : Nat := 1462824227754739134098429

theorem tailTrace_2848840 : CollatzResearch.WordTrace tailWord_2848840 prefixEnd_2848840 1462824227754739134098429 := by
  unfold tailWord_2848840
  simp only [CollatzResearch.WordTrace]
  refine ⟨51952865499573348990715987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69270487332764465320954649 51952865499573348990715987)
  ·
    refine ⟨77929298249360023486073981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51952865499573348990715987 77929298249360023486073981)
    ·
      refine ⟨29223486843510008807277743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 77929298249360023486073981 29223486843510008807277743)
      ·
        refine ⟨43835230265265013210916615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29223486843510008807277743 43835230265265013210916615)
        ·
          refine ⟨65752845397897519816374923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43835230265265013210916615 65752845397897519816374923)
          ·
            refine ⟨98629268096846279724562385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65752845397897519816374923 98629268096846279724562385)
            ·
              refine ⟨73971951072634709793421789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 98629268096846279724562385 73971951072634709793421789)
              ·
                refine ⟨27739481652238016172533171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 73971951072634709793421789 27739481652238016172533171)
                ·
                  refine ⟨41609222478357024258799757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27739481652238016172533171 41609222478357024258799757)
                  ·
                    refine ⟨15603458429383884097049909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 41609222478357024258799757 15603458429383884097049909)
                    ·
                      refine ⟨1462824227754739134098429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15603458429383884097049909 1462824227754739134098429)
                      ·
                        rfl

theorem cell23_2848840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 3, 1, 3, 5].length) (baseStart_2848840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2848840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2848840 prefixEnd_2848840 := by exact prefixLift 2848840
  have htrace : WordTrace (prefixWord ++ tailWord_2848840) baseStart_2848840 baseEnd_2848840 := by
    simpa [prefixWord, tailWord_2848840, baseEnd_2848840] using wordTrace_append hprefix tailTrace_2848840
  have hstable : (prefixWord ++ tailWord_2848840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2848840).length < 2 ^ (prefixWord ++ tailWord_2848840).sum := by decide
  have hdescent : baseEnd_2848840 < baseStart_2848840 := by decide
  rcases family_descends (prefixWord ++ tailWord_2848840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2848841 : List Nat := [1, 2, 1, 1, 2, 2, 7, 1, 1, 3, 2]
def baseStart_2848841 : Nat := 118140960795 + 2848841 * 2 ^ 59
def prefixEnd_2848841 : Nat := 4983230072969 + 3 ^ 40 * 2848841 * 2
def baseEnd_2848841 : Nat := 1462824741235393630185925

theorem tailTrace_2848841 : CollatzResearch.WordTrace tailWord_2848841 prefixEnd_2848841 1462824741235393630185925 := by
  unfold tailWord_2848841
  simp only [CollatzResearch.WordTrace]
  refine ⟨103905767472143075152218377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69270511648095383434812251 103905767472143075152218377)
  ·
    refine ⟨77929325604107306364163783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103905767472143075152218377 77929325604107306364163783)
    ·
      refine ⟨116893988406160959546245675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77929325604107306364163783 116893988406160959546245675)
      ·
        refine ⟨175340982609241439319368513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116893988406160959546245675 175340982609241439319368513)
        ·
          refine ⟨131505736956931079489526385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 175340982609241439319368513 131505736956931079489526385)
          ·
            refine ⟨98629302717698309617144789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 131505736956931079489526385 98629302717698309617144789)
            ·
              refine ⟨2311624282446054131651831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 98629302717698309617144789 2311624282446054131651831)
              ·
                refine ⟨3467436423669081197477747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2311624282446054131651831 3467436423669081197477747)
                ·
                  refine ⟨5201154635503621796216621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3467436423669081197477747 5201154635503621796216621)
                  ·
                    refine ⟨1950432988313858173581233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5201154635503621796216621 1950432988313858173581233)
                    ·
                      refine ⟨1462824741235393630185925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1950432988313858173581233 1462824741235393630185925)
                      ·
                        rfl

theorem cell23_2848841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 7, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 7, 1, 1, 3, 2].length) (baseStart_2848841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2848841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2848841 prefixEnd_2848841 := by exact prefixLift 2848841
  have htrace : WordTrace (prefixWord ++ tailWord_2848841) baseStart_2848841 baseEnd_2848841 := by
    simpa [prefixWord, tailWord_2848841, baseEnd_2848841] using wordTrace_append hprefix tailTrace_2848841
  have hstable : (prefixWord ++ tailWord_2848841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2848841).length < 2 ^ (prefixWord ++ tailWord_2848841).sum := by decide
  have hdescent : baseEnd_2848841 < baseStart_2848841 := by decide
  rcases family_descends (prefixWord ++ tailWord_2848841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2848871 : List Nat := [1, 1, 5, 1, 1, 2, 1, 5, 2, 2, 2]
def baseStart_2848871 : Nat := 118140960795 + 2848871 * 2 ^ 59
def prefixEnd_2848871 : Nat := 4983230072969 + 3 ^ 40 * 2848871 * 2
def baseEnd_2848871 : Nat := 1462840145655028512810787

theorem tailTrace_2848871 : CollatzResearch.WordTrace tailWord_2848871 prefixEnd_2848871 1462840145655028512810787 := by
  unfold tailWord_2848871
  simp only [CollatzResearch.WordTrace]
  refine ⟨103906861662034390275810467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69271241108022926850540311 103906861662034390275810467)
  ·
    refine ⟨155860292493051585413715701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103906861662034390275810467 155860292493051585413715701)
    ·
      refine ⟨14611902421223586132535847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 155860292493051585413715701 14611902421223586132535847)
      ·
        refine ⟨21917853631835379198803771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14611902421223586132535847 21917853631835379198803771)
        ·
          refine ⟨32876780447753068798205657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21917853631835379198803771 32876780447753068798205657)
          ·
            refine ⟨24657585335814801598654243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32876780447753068798205657 24657585335814801598654243)
            ·
              refine ⟨36986378003722202397981365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24657585335814801598654243 36986378003722202397981365)
              ·
                refine ⟨3467472937848956474810753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 36986378003722202397981365 3467472937848956474810753)
                ·
                  refine ⟨2600604703386717356108065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3467472937848956474810753 2600604703386717356108065)
                  ·
                    refine ⟨1950453527540038017081049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2600604703386717356108065 1950453527540038017081049)
                    ·
                      refine ⟨1462840145655028512810787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1950453527540038017081049 1462840145655028512810787)
                      ·
                        rfl

theorem cell23_2848871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 5, 2, 2, 2].length) (baseStart_2848871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2848871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2848871 prefixEnd_2848871 := by exact prefixLift 2848871
  have htrace : WordTrace (prefixWord ++ tailWord_2848871) baseStart_2848871 baseEnd_2848871 := by
    simpa [prefixWord, tailWord_2848871, baseEnd_2848871] using wordTrace_append hprefix tailTrace_2848871
  have hstable : (prefixWord ++ tailWord_2848871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2848871).length < 2 ^ (prefixWord ++ tailWord_2848871).sum := by decide
  have hdescent : baseEnd_2848871 < baseStart_2848871 := by decide
  rcases family_descends (prefixWord ++ tailWord_2848871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2848877 : List Nat := [1, 5, 1, 1, 2, 1, 3, 2, 7]
def baseStart_2848877 : Nat := 118140960795 + 2848877 * 2 ^ 59
def prefixEnd_2848877 : Nat := 4983230072969 + 3 ^ 40 * 2848877 * 2
def baseEnd_2848877 : Nat := 162538136282106165481751

theorem tailTrace_2848877 : CollatzResearch.WordTrace tailWord_2848877 prefixEnd_2848877 162538136282106165481751 := by
  unfold tailWord_2848877
  simp only [CollatzResearch.WordTrace]
  refine ⟨103907080500012653300528885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69271387000008435533685923 103907080500012653300528885)
  ·
    refine ⟨9741288796876186246924583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 103907080500012653300528885 9741288796876186246924583)
    ·
      refine ⟨14611933195314279370386875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9741288796876186246924583 14611933195314279370386875)
      ·
        refine ⟨21917899792971419055580313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14611933195314279370386875 21917899792971419055580313)
        ·
          refine ⟨16438424844728564291685235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21917899792971419055580313 16438424844728564291685235)
          ·
            refine ⟨24657637267092846437527853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16438424844728564291685235 24657637267092846437527853)
            ·
              refine ⟨9246613975159817414072945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24657637267092846437527853 9246613975159817414072945)
              ·
                refine ⟨6934960481369863060554709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9246613975159817414072945 6934960481369863060554709)
                ·
                  refine ⟨162538136282106165481751, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6934960481369863060554709 162538136282106165481751)
                  ·
                    rfl

theorem cell23_2848877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 3, 2, 7].length) (baseStart_2848877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2848877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2848877 prefixEnd_2848877 := by exact prefixLift 2848877
  have htrace : WordTrace (prefixWord ++ tailWord_2848877) baseStart_2848877 baseEnd_2848877 := by
    simpa [prefixWord, tailWord_2848877, baseEnd_2848877] using wordTrace_append hprefix tailTrace_2848877
  have hstable : (prefixWord ++ tailWord_2848877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2848877).length < 2 ^ (prefixWord ++ tailWord_2848877).sum := by decide
  have hdescent : baseEnd_2848877 < baseStart_2848877 := by decide
  rcases family_descends (prefixWord ++ tailWord_2848877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2848904 : List Nat := [2, 1, 3, 4, 1, 1, 1, 2, 2, 3, 3]
def baseStart_2848904 : Nat := 118140960795 + 2848904 * 2 ^ 59
def prefixEnd_2848904 : Nat := 4983230072969 + 3 ^ 40 * 2848904 * 2
def baseEnd_2848904 : Nat := 1462857090516626883698135

theorem tailTrace_2848904 : CollatzResearch.WordTrace tailWord_2848904 prefixEnd_2848904 1462857090516626883698135 := by
  unfold tailWord_2848904
  simp only [CollatzResearch.WordTrace]
  refine ⟨51954032635457418455880883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69272043513943224607841177 51954032635457418455880883)
  ·
    refine ⟨77931048953186127683821325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51954032635457418455880883 77931048953186127683821325)
    ·
      refine ⟨29224143357444797881432997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 77931048953186127683821325 29224143357444797881432997)
      ·
        refine ⟨5479526879520899602768687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29224143357444797881432997 5479526879520899602768687)
        ·
          refine ⟨8219290319281349404153031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5479526879520899602768687 8219290319281349404153031)
          ·
            refine ⟨12328935478922024106229547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8219290319281349404153031 12328935478922024106229547)
            ·
              refine ⟨18493403218383036159344321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12328935478922024106229547 18493403218383036159344321)
              ·
                refine ⟨13870052413787277119508241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18493403218383036159344321 13870052413787277119508241)
                ·
                  refine ⟨10402539310340457839631181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13870052413787277119508241 10402539310340457839631181)
                  ·
                    refine ⟨3900952241377671689861693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10402539310340457839631181 3900952241377671689861693)
                    ·
                      refine ⟨1462857090516626883698135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3900952241377671689861693 1462857090516626883698135)
                      ·
                        rfl

theorem cell23_2848904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 1, 2, 2, 3, 3].length) (baseStart_2848904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2848904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2848904 prefixEnd_2848904 := by exact prefixLift 2848904
  have htrace : WordTrace (prefixWord ++ tailWord_2848904) baseStart_2848904 baseEnd_2848904 := by
    simpa [prefixWord, tailWord_2848904, baseEnd_2848904] using wordTrace_append hprefix tailTrace_2848904
  have hstable : (prefixWord ++ tailWord_2848904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2848904).length < 2 ^ (prefixWord ++ tailWord_2848904).sum := by decide
  have hdescent : baseEnd_2848904 < baseStart_2848904 := by decide
  rcases family_descends (prefixWord ++ tailWord_2848904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2848984 : List Nat := [2, 1, 2, 2, 4, 2, 1, 3, 6]
def baseStart_2848984 : Nat := 118140960795 + 2848984 * 2 ^ 59
def prefixEnd_2848984 : Nat := 4983230072969 + 3 ^ 40 * 2848984 * 2
def baseEnd_2848984 : Nat := 162544240996554063410863

theorem tailTrace_2848984 : CollatzResearch.WordTrace tailWord_2848984 prefixEnd_2848984 162544240996554063410863 := by
  unfold tailWord_2848984
  simp only [CollatzResearch.WordTrace]
  refine ⟨51955491555312505287337003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69273988740416673716449337 51955491555312505287337003)
  ·
    refine ⟨77933237332968757931005505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51955491555312505287337003 77933237332968757931005505)
    ·
      refine ⟨58449927999726568448254129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77933237332968757931005505 58449927999726568448254129)
      ·
        refine ⟨43837445999794926336190597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58449927999726568448254129 43837445999794926336190597)
        ·
          refine ⟨8219521124961548688035737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 43837445999794926336190597 8219521124961548688035737)
          ·
            refine ⟨6164640843721161516026803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8219521124961548688035737 6164640843721161516026803)
            ·
              refine ⟨9246961265581742274040205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6164640843721161516026803 9246961265581742274040205)
              ·
                refine ⟨3467610474593153352765077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9246961265581742274040205 3467610474593153352765077)
                ·
                  refine ⟨162544240996554063410863, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3467610474593153352765077 162544240996554063410863)
                  ·
                    rfl

theorem cell23_2848984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 1, 3, 6].length) (baseStart_2848984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2848984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2848984 prefixEnd_2848984 := by exact prefixLift 2848984
  have htrace : WordTrace (prefixWord ++ tailWord_2848984) baseStart_2848984 baseEnd_2848984 := by
    simpa [prefixWord, tailWord_2848984, baseEnd_2848984] using wordTrace_append hprefix tailTrace_2848984
  have hstable : (prefixWord ++ tailWord_2848984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2848984).length < 2 ^ (prefixWord ++ tailWord_2848984).sum := by decide
  have hdescent : baseEnd_2848984 < baseStart_2848984 := by decide
  rcases family_descends (prefixWord ++ tailWord_2848984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2849027 : List Nat := [1, 1, 1, 3, 2, 3, 1, 2, 3, 6]
def baseStart_2849027 : Nat := 118140960795 + 2849027 * 2 ^ 59
def prefixEnd_2849027 : Nat := 4983230072969 + 3 ^ 40 * 2849027 * 2
def baseEnd_2849027 : Nat := 487640082879043300820023

theorem tailTrace_2849027 : CollatzResearch.WordTrace tailWord_2849027 prefixEnd_2849027 487640082879043300820023 := by
  unfold tailWord_2849027
  simp only [CollatzResearch.WordTrace]
  refine ⟨103912551449469228918489335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69275034299646152612326223 103912551449469228918489335)
  ·
    refine ⟨155868827174203843377734003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103912551449469228918489335 155868827174203843377734003)
    ·
      refine ⟨233803240761305765066601005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155868827174203843377734003 233803240761305765066601005)
      ·
        refine ⟨87676215285489661899975377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 233803240761305765066601005 87676215285489661899975377)
        ·
          refine ⟨65757161464117246424981533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87676215285489661899975377 65757161464117246424981533)
          ·
            refine ⟨24658935549043967409368075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 65757161464117246424981533 24658935549043967409368075)
            ·
              refine ⟨36988403323565951114052113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24658935549043967409368075 36988403323565951114052113)
              ·
                refine ⟨27741302492674463335539085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36988403323565951114052113 27741302492674463335539085)
                ·
                  refine ⟨10402988434752923750827157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27741302492674463335539085 10402988434752923750827157)
                  ·
                    refine ⟨487640082879043300820023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10402988434752923750827157 487640082879043300820023)
                    ·
                      rfl

theorem cell23_2849027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 2, 3, 6].length) (baseStart_2849027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2849027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2849027 prefixEnd_2849027 := by exact prefixLift 2849027
  have htrace : WordTrace (prefixWord ++ tailWord_2849027) baseStart_2849027 baseEnd_2849027 := by
    simpa [prefixWord, tailWord_2849027, baseEnd_2849027] using wordTrace_append hprefix tailTrace_2849027
  have hstable : (prefixWord ++ tailWord_2849027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2849027).length < 2 ^ (prefixWord ++ tailWord_2849027).sum := by decide
  have hdescent : baseEnd_2849027 < baseStart_2849027 := by decide
  rcases family_descends (prefixWord ++ tailWord_2849027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2849034 : List Nat := [3, 1, 2, 2, 1, 1, 3, 2, 3, 1, 4]
def baseStart_2849034 : Nat := 118140960795 + 2849034 * 2 ^ 59
def prefixEnd_2849034 : Nat := 4983230072969 + 3 ^ 40 * 2849034 * 2
def baseEnd_2849034 : Nat := 1462923843001711375072537

theorem tailTrace_2849034 : CollatzResearch.WordTrace tailWord_2849034 prefixEnd_2849034 1462923843001711375072537 := by
  unfold tailWord_2849034
  simp only [CollatzResearch.WordTrace]
  refine ⟨25978201690110967278498539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69275204506962579409329437 25978201690110967278498539)
  ·
    refine ⟨38967302535166450917747809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25978201690110967278498539 38967302535166450917747809)
    ·
      refine ⟨29225476901374838188310857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38967302535166450917747809 29225476901374838188310857)
      ·
        refine ⟨21919107676031128641233143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29225476901374838188310857 21919107676031128641233143)
        ·
          refine ⟨32878661514046692961849715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21919107676031128641233143 32878661514046692961849715)
          ·
            refine ⟨49317992271070039442774573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32878661514046692961849715 49317992271070039442774573)
            ·
              refine ⟨18494247101651264791040465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49317992271070039442774573 18494247101651264791040465)
              ·
                refine ⟨13870685326238448593280349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18494247101651264791040465 13870685326238448593280349)
                ·
                  refine ⟨5201506997339418222480131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13870685326238448593280349 5201506997339418222480131)
                  ·
                    refine ⟨7802260496009127333720197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5201506997339418222480131 7802260496009127333720197)
                    ·
                      refine ⟨1462923843001711375072537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7802260496009127333720197 1462923843001711375072537)
                      ·
                        rfl

theorem cell23_2849034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 3, 2, 3, 1, 4].length) (baseStart_2849034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2849034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2849034 prefixEnd_2849034 := by exact prefixLift 2849034
  have htrace : WordTrace (prefixWord ++ tailWord_2849034) baseStart_2849034 baseEnd_2849034 := by
    simpa [prefixWord, tailWord_2849034, baseEnd_2849034] using wordTrace_append hprefix tailTrace_2849034
  have hstable : (prefixWord ++ tailWord_2849034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2849034).length < 2 ^ (prefixWord ++ tailWord_2849034).sum := by decide
  have hdescent : baseEnd_2849034 < baseStart_2849034 := by decide
  rcases family_descends (prefixWord ++ tailWord_2849034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2849051 : List Nat := [1, 1, 1, 1, 1, 1, 7, 1, 5, 2, 2]
def baseStart_2849051 : Nat := 118140960795 + 2849051 * 2 ^ 59
def prefixEnd_2849051 : Nat := 4983230072969 + 3 ^ 40 * 2849051 * 2
def baseEnd_2849051 : Nat := 1462932572172837808559959

theorem tailTrace_2849051 : CollatzResearch.WordTrace tailWord_2849051 prefixEnd_2849051 1462932572172837808559959 := by
  unfold tailWord_2849051
  simp only [CollatzResearch.WordTrace]
  refine ⟨103913426801382281017363007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69275617867588187344908671 103913426801382281017363007)
  ·
    refine ⟨155870140202073421526044511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103913426801382281017363007 155870140202073421526044511)
    ·
      refine ⟨233805210303110132289066767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155870140202073421526044511 233805210303110132289066767)
      ·
        refine ⟨350707815454665198433600151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 233805210303110132289066767 350707815454665198433600151)
        ·
          refine ⟨526061723181997797650400227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 350707815454665198433600151 526061723181997797650400227)
          ·
            refine ⟨789092584772996696475600341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 526061723181997797650400227 789092584772996696475600341)
            ·
              refine ⟨18494357455617110073646883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 789092584772996696475600341 18494357455617110073646883)
              ·
                refine ⟨27741536183425665110470325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18494357455617110073646883 27741536183425665110470325)
                ·
                  refine ⟨2600769017196156104106593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 27741536183425665110470325 2600769017196156104106593)
                  ·
                    refine ⟨1950576762897117078079945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2600769017196156104106593 1950576762897117078079945)
                    ·
                      refine ⟨1462932572172837808559959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1950576762897117078079945 1462932572172837808559959)
                      ·
                        rfl

theorem cell23_2849051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 7, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 7, 1, 5, 2, 2].length) (baseStart_2849051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2849051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2849051 prefixEnd_2849051 := by exact prefixLift 2849051
  have htrace : WordTrace (prefixWord ++ tailWord_2849051) baseStart_2849051 baseEnd_2849051 := by
    simpa [prefixWord, tailWord_2849051, baseEnd_2849051] using wordTrace_append hprefix tailTrace_2849051
  have hstable : (prefixWord ++ tailWord_2849051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2849051).length < 2 ^ (prefixWord ++ tailWord_2849051).sum := by decide
  have hdescent : baseEnd_2849051 < baseStart_2849051 := by decide
  rcases family_descends (prefixWord ++ tailWord_2849051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2849057 : List Nat := [1, 2, 3, 2, 1, 1, 2, 11]
def baseStart_2849057 : Nat := 118140960795 + 2849057 * 2 ^ 59
def prefixEnd_2849057 : Nat := 4983230072969 + 3 ^ 40 * 2849057 * 2
def baseEnd_2849057 : Nat := 54182801965065362410553

theorem tailTrace_2849057 : CollatzResearch.WordTrace tailWord_2849057 prefixEnd_2849057 54182801965065362410553 := by
  unfold tailWord_2849057
  simp only [CollatzResearch.WordTrace]
  refine ⟨103913645639360544042081425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69275763759573696028054283 103913645639360544042081425)
  ·
    refine ⟨77935234229520408031561069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103913645639360544042081425 77935234229520408031561069)
    ·
      refine ⟨29225712836070153011835401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 77935234229520408031561069 29225712836070153011835401)
      ·
        refine ⟨21919284627052614758876551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29225712836070153011835401 21919284627052614758876551)
        ·
          refine ⟨32878926940578922138314827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21919284627052614758876551 32878926940578922138314827)
          ·
            refine ⟨49318390410868383207472241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32878926940578922138314827 49318390410868383207472241)
            ·
              refine ⟨36988792808151287405604181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49318390410868383207472241 36988792808151287405604181)
              ·
                refine ⟨54182801965065362410553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 36988792808151287405604181 54182801965065362410553)
                ·
                  rfl

theorem cell23_2849057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 11].length) (baseStart_2849057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2849057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2849057 prefixEnd_2849057 := by exact prefixLift 2849057
  have htrace : WordTrace (prefixWord ++ tailWord_2849057) baseStart_2849057 baseEnd_2849057 := by
    simpa [prefixWord, tailWord_2849057, baseEnd_2849057] using wordTrace_append hprefix tailTrace_2849057
  have hstable : (prefixWord ++ tailWord_2849057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2849057).length < 2 ^ (prefixWord ++ tailWord_2849057).sum := by decide
  have hdescent : baseEnd_2849057 < baseStart_2849057 := by decide
  rcases family_descends (prefixWord ++ tailWord_2849057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2849074 : List Nat := [3, 2, 1, 1, 5, 1, 10]
def baseStart_2849074 : Nat := 118140960795 + 2849074 * 2 ^ 59
def prefixEnd_2849074 : Nat := 4983230072969 + 3 ^ 40 * 2849074 * 2
def baseEnd_2849074 : Nat := 18061041755899891587313

theorem tailTrace_2849074 : CollatzResearch.WordTrace tailWord_2849074 prefixEnd_2849074 18061041755899891587313 := by
  unfold tailWord_2849074
  simp only [CollatzResearch.WordTrace]
  refine ⟨25978566420074738986362569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69276177120199303963633517 25978566420074738986362569)
  ·
    refine ⟨19483924815056054239771927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25978566420074738986362569 19483924815056054239771927)
    ·
      refine ⟨29225887222584081359657891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19483924815056054239771927 29225887222584081359657891)
      ·
        refine ⟨43838830833876122039486837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29225887222584081359657891 43838830833876122039486837)
        ·
          refine ⟨4109890390675886441201891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 43838830833876122039486837 4109890390675886441201891)
          ·
            refine ⟨6164835586013829661802837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4109890390675886441201891 6164835586013829661802837)
            ·
              refine ⟨18061041755899891587313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 6164835586013829661802837 18061041755899891587313)
              ·
                rfl

theorem cell23_2849074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 10].length) (baseStart_2849074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2849074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2849074 prefixEnd_2849074 := by exact prefixLift 2849074
  have htrace : WordTrace (prefixWord ++ tailWord_2849074) baseStart_2849074 baseEnd_2849074 := by
    simpa [prefixWord, tailWord_2849074, baseEnd_2849074] using wordTrace_append hprefix tailTrace_2849074
  have hstable : (prefixWord ++ tailWord_2849074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2849074).length < 2 ^ (prefixWord ++ tailWord_2849074).sum := by decide
  have hdescent : baseEnd_2849074 < baseStart_2849074 := by decide
  rcases family_descends (prefixWord ++ tailWord_2849074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2849107 : List Nat := [1, 1, 1, 2, 1, 1, 4, 1, 1, 2, 8]
def baseStart_2849107 : Nat := 118140960795 + 2849107 * 2 ^ 59
def prefixEnd_2849107 : Nat := 4983230072969 + 3 ^ 40 * 2849107 * 2
def baseEnd_2849107 : Nat := 1462961327089489589459701

theorem tailTrace_2849107 : CollatzResearch.WordTrace tailWord_2849107 prefixEnd_2849107 1462961327089489589459701 := by
  unfold tailWord_2849107
  simp only [CollatzResearch.WordTrace]
  refine ⟨103915469289179402581401575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69276979526119601720934383 103915469289179402581401575)
  ·
    refine ⟨155873203933769103872102363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103915469289179402581401575 155873203933769103872102363)
    ·
      refine ⟨233809805900653655808153545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155873203933769103872102363 233809805900653655808153545)
      ·
        refine ⟨175357354425490241856115159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 233809805900653655808153545 175357354425490241856115159)
        ·
          refine ⟨263036031638235362784172739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 175357354425490241856115159 263036031638235362784172739)
          ·
            refine ⟨394554047457353044176259109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 263036031638235362784172739 394554047457353044176259109)
            ·
              refine ⟨73978883898253695783048583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 394554047457353044176259109 73978883898253695783048583)
              ·
                refine ⟨110968325847380543674572875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 73978883898253695783048583 110968325847380543674572875)
                ·
                  refine ⟨166452488771070815511859313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 110968325847380543674572875 166452488771070815511859313)
                  ·
                    refine ⟨124839366578303111633894485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 166452488771070815511859313 124839366578303111633894485)
                    ·
                      refine ⟨1462961327089489589459701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 124839366578303111633894485 1462961327089489589459701)
                      ·
                        rfl

theorem cell23_2849107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 1, 1, 2, 8].length) (baseStart_2849107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2849107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2849107 prefixEnd_2849107 := by exact prefixLift 2849107
  have htrace : WordTrace (prefixWord ++ tailWord_2849107) baseStart_2849107 baseEnd_2849107 := by
    simpa [prefixWord, tailWord_2849107, baseEnd_2849107] using wordTrace_append hprefix tailTrace_2849107
  have hstable : (prefixWord ++ tailWord_2849107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2849107).length < 2 ^ (prefixWord ++ tailWord_2849107).sum := by decide
  have hdescent : baseEnd_2849107 < baseStart_2849107 := by decide
  rcases family_descends (prefixWord ++ tailWord_2849107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2849192 : List Nat := [2, 1, 6, 1, 1, 1, 1, 4, 2, 2, 2]
def baseStart_2849192 : Nat := 118140960795 + 2849192 * 2 ^ 59
def prefixEnd_2849192 : Nat := 4983230072969 + 3 ^ 40 * 2849192 * 2
def baseEnd_2849192 : Nat := 1463004972945121756896811

theorem tailTrace_2849192 : CollatzResearch.WordTrace tailWord_2849192 prefixEnd_2849192 1463004972945121756896811 := by
  unfold tailWord_2849192
  simp only [CollatzResearch.WordTrace]
  refine ⟨51959284746935731049122915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69279046329247641398830553 51959284746935731049122915)
  ·
    refine ⟨77938927120403596573684373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51959284746935731049122915 77938927120403596573684373)
    ·
      refine ⟨3653387208768918589391455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 77938927120403596573684373 3653387208768918589391455)
      ·
        refine ⟨5480080813153377884087183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3653387208768918589391455 5480080813153377884087183)
        ·
          refine ⟨8220121219730066826130775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5480080813153377884087183 8220121219730066826130775)
          ·
            refine ⟨12330181829595100239196163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8220121219730066826130775 12330181829595100239196163)
            ·
              refine ⟨18495272744392650358794245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12330181829595100239196163 18495272744392650358794245)
              ·
                refine ⟨3467863639573621942273921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18495272744392650358794245 3467863639573621942273921)
                ·
                  refine ⟨2600897729680216456705441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3467863639573621942273921 2600897729680216456705441)
                  ·
                    refine ⟨1950673297260162342529081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2600897729680216456705441 1950673297260162342529081)
                    ·
                      refine ⟨1463004972945121756896811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1950673297260162342529081 1463004972945121756896811)
                      ·
                        rfl

theorem cell23_2849192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 1, 4, 2, 2, 2].length) (baseStart_2849192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2849192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2849192 prefixEnd_2849192 := by exact prefixLift 2849192
  have htrace : WordTrace (prefixWord ++ tailWord_2849192) baseStart_2849192 baseEnd_2849192 := by
    simpa [prefixWord, tailWord_2849192, baseEnd_2849192] using wordTrace_append hprefix tailTrace_2849192
  have hstable : (prefixWord ++ tailWord_2849192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2849192).length < 2 ^ (prefixWord ++ tailWord_2849192).sum := by decide
  have hdescent : baseEnd_2849192 < baseStart_2849192 := by decide
  rcases family_descends (prefixWord ++ tailWord_2849192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2849231 : List Nat := [1, 1, 2, 1, 1, 4, 1, 1, 3, 6, 2]
def baseStart_2849231 : Nat := 118140960795 + 2849231 * 2 ^ 59
def prefixEnd_2849231 : Nat := 4983230072969 + 3 ^ 40 * 2849231 * 2
def baseEnd_2849231 : Nat := 1463024998690647104309131

theorem tailTrace_2849231 : CollatzResearch.WordTrace tailWord_2849231 prefixEnd_2849231 1463024998690647104309131 := by
  unfold tailWord_2849231
  simp only [CollatzResearch.WordTrace]
  refine ⟨103919991940730171758915547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69279994627153447839277031 103919991940730171758915547)
  ·
    refine ⟨155879987911095257638373321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103919991940730171758915547 155879987911095257638373321)
    ·
      refine ⟨116909990933321443228779991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 155879987911095257638373321 116909990933321443228779991)
      ·
        refine ⟨175364986399982164843169987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116909990933321443228779991 175364986399982164843169987)
        ·
          refine ⟨263047479599973247264754981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 175364986399982164843169987 263047479599973247264754981)
          ·
            refine ⟨49321402424994983862141559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 263047479599973247264754981 49321402424994983862141559)
            ·
              refine ⟨73982103637492475793212339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49321402424994983862141559 73982103637492475793212339)
              ·
                refine ⟨110973155456238713689818509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 73982103637492475793212339 110973155456238713689818509)
                ·
                  refine ⟨41614933296089517633681941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 110973155456238713689818509 41614933296089517633681941)
                  ·
                    refine ⟨1950699998254196139078841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 41614933296089517633681941 1950699998254196139078841)
                    ·
                      refine ⟨1463024998690647104309131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1950699998254196139078841 1463024998690647104309131)
                      ·
                        rfl

theorem cell23_2849231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 1, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 1, 3, 6, 2].length) (baseStart_2849231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2849231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2849231 prefixEnd_2849231 := by exact prefixLift 2849231
  have htrace : WordTrace (prefixWord ++ tailWord_2849231) baseStart_2849231 baseEnd_2849231 := by
    simpa [prefixWord, tailWord_2849231, baseEnd_2849231] using wordTrace_append hprefix tailTrace_2849231
  have hstable : (prefixWord ++ tailWord_2849231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2849231).length < 2 ^ (prefixWord ++ tailWord_2849231).sum := by decide
  have hdescent : baseEnd_2849231 < baseStart_2849231 := by decide
  rcases family_descends (prefixWord ++ tailWord_2849231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2849241 : List Nat := [1, 2, 1, 2, 4, 1, 1, 2, 5, 4]
def baseStart_2849241 : Nat := 118140960795 + 2849241 * 2 ^ 59
def prefixEnd_2849241 : Nat := 4983230072969 + 3 ^ 40 * 2849241 * 2
def baseEnd_2849241 : Nat := 487676711165730688394695

theorem tailTrace_2849241 : CollatzResearch.WordTrace tailWord_2849241 prefixEnd_2849241 487676711165730688394695 := by
  unfold tailWord_2849241
  simp only [CollatzResearch.WordTrace]
  refine ⟨103920356670693943466779577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69280237780462628977853051 103920356670693943466779577)
  ·
    refine ⟨77940267503020457600084683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103920356670693943466779577 77940267503020457600084683)
    ·
      refine ⟨116910401254530686400127025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77940267503020457600084683 116910401254530686400127025)
      ·
        refine ⟨87682800940898014800095269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 116910401254530686400127025 87682800940898014800095269)
        ·
          refine ⟨16440525176418377775017863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 87682800940898014800095269 16440525176418377775017863)
          ·
            refine ⟨24660787764627566662526795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16440525176418377775017863 24660787764627566662526795)
            ·
              refine ⟨36991181646941349993790193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24660787764627566662526795 36991181646941349993790193)
              ·
                refine ⟨27743386235206012495342645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36991181646941349993790193 27743386235206012495342645)
                ·
                  refine ⟨2600942459550563671438373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 27743386235206012495342645 2600942459550563671438373)
                  ·
                    refine ⟨487676711165730688394695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2600942459550563671438373 487676711165730688394695)
                    ·
                      rfl

theorem cell23_2849241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 2, 5, 4].length) (baseStart_2849241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2849241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2849241 prefixEnd_2849241 := by exact prefixLift 2849241
  have htrace : WordTrace (prefixWord ++ tailWord_2849241) baseStart_2849241 baseEnd_2849241 := by
    simpa [prefixWord, tailWord_2849241, baseEnd_2849241] using wordTrace_append hprefix tailTrace_2849241
  have hstable : (prefixWord ++ tailWord_2849241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2849241).length < 2 ^ (prefixWord ++ tailWord_2849241).sum := by decide
  have hdescent : baseEnd_2849241 < baseStart_2849241 := by decide
  rcases family_descends (prefixWord ++ tailWord_2849241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2849258 : List Nat := [3, 1, 3, 1, 3, 1, 1, 3, 3, 4]
def baseStart_2849258 : Nat := 118140960795 + 2849258 * 2 ^ 59
def prefixEnd_2849258 : Nat := 4983230072969 + 3 ^ 40 * 2849258 * 2
def baseEnd_2849258 : Nat := 487679620889439499557169

theorem tailTrace_2849258 : CollatzResearch.WordTrace tailWord_2849258 prefixEnd_2849258 487679620889439499557169 := by
  unfold tailWord_2849258
  simp only [CollatzResearch.WordTrace]
  refine ⟨25980244177908088842537107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69280651141088236913432285 25980244177908088842537107)
  ·
    refine ⟨38970366266862133263805661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25980244177908088842537107 38970366266862133263805661)
    ·
      refine ⟨14613887350073299973927123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38970366266862133263805661 14613887350073299973927123)
      ·
        refine ⟨21920831025109949960890685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14613887350073299973927123 21920831025109949960890685)
        ·
          refine ⟨8220311634416231235334007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21920831025109949960890685 8220311634416231235334007)
          ·
            refine ⟨12330467451624346853001011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8220311634416231235334007 12330467451624346853001011)
            ·
              refine ⟨18495701177436520279501517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12330467451624346853001011 18495701177436520279501517)
              ·
                refine ⟨6935887941538695104813069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18495701177436520279501517 6935887941538695104813069)
                ·
                  refine ⟨2600957978077010664304901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6935887941538695104813069 2600957978077010664304901)
                  ·
                    refine ⟨487679620889439499557169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2600957978077010664304901 487679620889439499557169)
                    ·
                      rfl

theorem cell23_2849258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 1, 3, 3, 4].length) (baseStart_2849258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2849258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2849258 prefixEnd_2849258 := by exact prefixLift 2849258
  have htrace : WordTrace (prefixWord ++ tailWord_2849258) baseStart_2849258 baseEnd_2849258 := by
    simpa [prefixWord, tailWord_2849258, baseEnd_2849258] using wordTrace_append hprefix tailTrace_2849258
  have hstable : (prefixWord ++ tailWord_2849258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2849258).length < 2 ^ (prefixWord ++ tailWord_2849258).sum := by decide
  have hdescent : baseEnd_2849258 < baseStart_2849258 := by decide
  rcases family_descends (prefixWord ++ tailWord_2849258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2849292 : List Nat := [2, 2, 1, 2, 4, 3, 1, 3, 1, 4]
def baseStart_2849292 : Nat := 118140960795 + 2849292 * 2 ^ 59
def prefixEnd_2849292 : Nat := 4983230072969 + 3 ^ 40 * 2849292 * 2
def baseEnd_2849292 : Nat := 487685440336857121882117

theorem tailTrace_2849292 : CollatzResearch.WordTrace tailWord_2849292 prefixEnd_2849292 487685440336857121882117 := by
  unfold tailWord_2849292
  simp only [CollatzResearch.WordTrace]
  refine ⟨51961108396754589588443065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69281477862339452784590753 51961108396754589588443065)
  ·
    refine ⟨38970831297565942191332299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51961108396754589588443065 38970831297565942191332299)
    ·
      refine ⟨58456246946348913286998449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38970831297565942191332299 58456246946348913286998449)
      ·
        refine ⟨43842185209761684965248837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58456246946348913286998449 43842185209761684965248837)
        ·
          refine ⟨8220409726830315930984157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 43842185209761684965248837 8220409726830315930984157)
          ·
            refine ⟨3082653647561368474119059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8220409726830315930984157 3082653647561368474119059)
            ·
              refine ⟨4623980471342052711178589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3082653647561368474119059 4623980471342052711178589)
              ·
                refine ⟨1733992676753269766691971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4623980471342052711178589 1733992676753269766691971)
                ·
                  refine ⟨2600989015129904650037957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1733992676753269766691971 2600989015129904650037957)
                  ·
                    refine ⟨487685440336857121882117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2600989015129904650037957 487685440336857121882117)
                    ·
                      rfl

theorem cell23_2849292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 3, 1, 3, 1, 4].length) (baseStart_2849292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2849292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2849292 prefixEnd_2849292 := by exact prefixLift 2849292
  have htrace : WordTrace (prefixWord ++ tailWord_2849292) baseStart_2849292 baseEnd_2849292 := by
    simpa [prefixWord, tailWord_2849292, baseEnd_2849292] using wordTrace_append hprefix tailTrace_2849292
  have hstable : (prefixWord ++ tailWord_2849292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2849292).length < 2 ^ (prefixWord ++ tailWord_2849292).sum := by decide
  have hdescent : baseEnd_2849292 < baseStart_2849292 := by decide
  rcases family_descends (prefixWord ++ tailWord_2849292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2849315 : List Nat := [1, 1, 1, 4, 4, 1, 3, 1, 3, 1, 3]
def baseStart_2849315 : Nat := 118140960795 + 2849315 * 2 ^ 59
def prefixEnd_2849315 : Nat := 4983230072969 + 3 ^ 40 * 2849315 * 2
def baseEnd_2849315 : Nat := 1463068131065624775658745

theorem tailTrace_2849315 : CollatzResearch.WordTrace tailWord_2849315 prefixEnd_2849315 1463068131065624775658745 := by
  unfold tailWord_2849315
  simp only [CollatzResearch.WordTrace]
  refine ⟨103923055672425854104973399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69282037114950569403315599 103923055672425854104973399)
  ·
    refine ⟨155884583508638781157460099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103923055672425854104973399 155884583508638781157460099)
    ·
      refine ⟨233826875262958171736190149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155884583508638781157460099 233826875262958171736190149)
      ·
        refine ⟨43842539111804657200535653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 233826875262958171736190149 43842539111804657200535653)
        ·
          refine ⟨8220476083463373225100435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 43842539111804657200535653 8220476083463373225100435)
          ·
            refine ⟨12330714125195059837650653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8220476083463373225100435 12330714125195059837650653)
            ·
              refine ⟨4624017796948147439118995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12330714125195059837650653 4624017796948147439118995)
              ·
                refine ⟨6936026695422221158678493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4624017796948147439118995 6936026695422221158678493)
                ·
                  refine ⟨2601010010783332934504435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6936026695422221158678493 2601010010783332934504435)
                  ·
                    refine ⟨3901515016174999401756653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2601010010783332934504435 3901515016174999401756653)
                    ·
                      refine ⟨1463068131065624775658745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3901515016174999401756653 1463068131065624775658745)
                      ·
                        rfl

theorem cell23_2849315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 3, 1, 3, 1, 3].length) (baseStart_2849315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2849315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2849315 prefixEnd_2849315 := by exact prefixLift 2849315
  have htrace : WordTrace (prefixWord ++ tailWord_2849315) baseStart_2849315 baseEnd_2849315 := by
    simpa [prefixWord, tailWord_2849315, baseEnd_2849315] using wordTrace_append hprefix tailTrace_2849315
  have hstable : (prefixWord ++ tailWord_2849315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2849315).length < 2 ^ (prefixWord ++ tailWord_2849315).sum := by decide
  have hdescent : baseEnd_2849315 < baseStart_2849315 := by decide
  rcases family_descends (prefixWord ++ tailWord_2849315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2849331 : List Nat := [1, 1, 1, 2, 4, 2, 2, 3, 1, 6]
def baseStart_2849331 : Nat := 118140960795 + 2849331 * 2 ^ 59
def prefixEnd_2849331 : Nat := 4983230072969 + 3 ^ 40 * 2849331 * 2
def baseEnd_2849331 : Nat := 487692115585365571019557

theorem tailTrace_2849331 : CollatzResearch.WordTrace tailWord_2849331 prefixEnd_2849331 487692115585365571019557 := by
  unfold tailWord_2849331
  simp only [CollatzResearch.WordTrace]
  refine ⟨103923639240367888837555847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69282426160245259225037231 103923639240367888837555847)
  ·
    refine ⟨155885458860551833256333771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103923639240367888837555847 155885458860551833256333771)
    ·
      refine ⟨233828188290827749884500657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155885458860551833256333771 233828188290827749884500657)
      ·
        refine ⟨175371141218120812413375493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 233828188290827749884500657 175371141218120812413375493)
        ·
          refine ⟨32882088978397652327507905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 175371141218120812413375493 32882088978397652327507905)
          ·
            refine ⟨24661566733798239245630929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32882088978397652327507905 24661566733798239245630929)
            ·
              refine ⟨18496175050348679434223197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24661566733798239245630929 18496175050348679434223197)
              ·
                refine ⟨6936065643880754787833699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18496175050348679434223197 6936065643880754787833699)
                ·
                  refine ⟨10404098465821132181750549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6936065643880754787833699 10404098465821132181750549)
                  ·
                    refine ⟨487692115585365571019557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10404098465821132181750549 487692115585365571019557)
                    ·
                      rfl

theorem cell23_2849331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 2, 3, 1, 6].length) (baseStart_2849331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2849331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2849331 prefixEnd_2849331 := by exact prefixLift 2849331
  have htrace : WordTrace (prefixWord ++ tailWord_2849331) baseStart_2849331 baseEnd_2849331 := by
    simpa [prefixWord, tailWord_2849331, baseEnd_2849331] using wordTrace_append hprefix tailTrace_2849331
  have hstable : (prefixWord ++ tailWord_2849331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2849331).length < 2 ^ (prefixWord ++ tailWord_2849331).sum := by decide
  have hdescent : baseEnd_2849331 < baseStart_2849331 := by decide
  rcases family_descends (prefixWord ++ tailWord_2849331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2849338 : List Nat := [3, 1, 1, 1, 3, 4, 1, 1, 3, 1, 4]
def baseStart_2849338 : Nat := 118140960795 + 2849338 * 2 ^ 59
def prefixEnd_2849338 : Nat := 4983230072969 + 3 ^ 40 * 2849338 * 2
def baseEnd_2849338 : Nat := 1463079941120678185671139

theorem tailTrace_2849338 : CollatzResearch.WordTrace tailWord_2849338 prefixEnd_2849338 1463079941120678185671139 := by
  unfold tailWord_2849338
  simp only [CollatzResearch.WordTrace]
  refine ⟨25980973637835632258265167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69282596367561686022040445 25980973637835632258265167)
  ·
    refine ⟨38971460456753448387397751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25980973637835632258265167 38971460456753448387397751)
    ·
      refine ⟨58457190685130172581096627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38971460456753448387397751 58457190685130172581096627)
      ·
        refine ⟨87685786027695258871644941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58457190685130172581096627 87685786027695258871644941)
        ·
          refine ⟨32882169760385722076866853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 87685786027695258871644941 32882169760385722076866853)
          ·
            refine ⟨6165406830072322889412535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32882169760385722076866853 6165406830072322889412535)
            ·
              refine ⟨9248110245108484334118803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6165406830072322889412535 9248110245108484334118803)
              ·
                refine ⟨13872165367662726501178205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9248110245108484334118803 13872165367662726501178205)
                ·
                  refine ⟨5202062012873522437941827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13872165367662726501178205 5202062012873522437941827)
                  ·
                    refine ⟨7803093019310283656912741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5202062012873522437941827 7803093019310283656912741)
                    ·
                      refine ⟨1463079941120678185671139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7803093019310283656912741 1463079941120678185671139)
                      ·
                        rfl

theorem cell23_2849338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 1, 1, 3, 1, 4].length) (baseStart_2849338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2849338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2849338 prefixEnd_2849338 := by exact prefixLift 2849338
  have htrace : WordTrace (prefixWord ++ tailWord_2849338) baseStart_2849338 baseEnd_2849338 := by
    simpa [prefixWord, tailWord_2849338, baseEnd_2849338] using wordTrace_append hprefix tailTrace_2849338
  have hstable : (prefixWord ++ tailWord_2849338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2849338).length < 2 ^ (prefixWord ++ tailWord_2849338).sum := by decide
  have hdescent : baseEnd_2849338 < baseStart_2849338 := by decide
  rcases family_descends (prefixWord ++ tailWord_2849338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2849358 : List Nat := [4, 1, 1, 1, 1, 2, 5, 1, 1, 1, 5]
def baseStart_2849358 : Nat := 118140960795 + 2849358 * 2 ^ 59
def prefixEnd_2849358 : Nat := 4983230072969 + 3 ^ 40 * 2849358 * 2
def baseEnd_2849358 : Nat := 1463090210733768107421047

theorem tailTrace_2849358 : CollatzResearch.WordTrace tailWord_2849358 prefixEnd_2849358 1463090210733768107421047 := by
  unfold tailWord_2849358
  simp only [CollatzResearch.WordTrace]
  refine ⟨12990578001408759056098591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 69283082674180048299192485 12990578001408759056098591)
  ·
    refine ⟨19485867002113138584147887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12990578001408759056098591 19485867002113138584147887)
    ·
      refine ⟨29228800503169707876221831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19485867002113138584147887 29228800503169707876221831)
      ·
        refine ⟨43843200754754561814332747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29228800503169707876221831 43843200754754561814332747)
        ·
          refine ⟨65764801132131842721499121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43843200754754561814332747 65764801132131842721499121)
          ·
            refine ⟨49323600849098882041124341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65764801132131842721499121 49323600849098882041124341)
            ·
              refine ⟨4624087579603020191355407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 49323600849098882041124341 4624087579603020191355407)
              ·
                refine ⟨6936131369404530287033111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4624087579603020191355407 6936131369404530287033111)
                ·
                  refine ⟨10404197054106795430549667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6936131369404530287033111 10404197054106795430549667)
                  ·
                    refine ⟨15606295581160193145824501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10404197054106795430549667 15606295581160193145824501)
                    ·
                      refine ⟨1463090210733768107421047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15606295581160193145824501 1463090210733768107421047)
                      ·
                        rfl

theorem cell23_2849358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 5, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 5, 1, 1, 1, 5].length) (baseStart_2849358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2849358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2849358 prefixEnd_2849358 := by exact prefixLift 2849358
  have htrace : WordTrace (prefixWord ++ tailWord_2849358) baseStart_2849358 baseEnd_2849358 := by
    simpa [prefixWord, tailWord_2849358, baseEnd_2849358] using wordTrace_append hprefix tailTrace_2849358
  have hstable : (prefixWord ++ tailWord_2849358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2849358).length < 2 ^ (prefixWord ++ tailWord_2849358).sum := by decide
  have hdescent : baseEnd_2849358 < baseStart_2849358 := by decide
  rcases family_descends (prefixWord ++ tailWord_2849358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2849388 : List Nat := [2, 2, 1, 1, 3, 1, 3, 3, 1, 3, 3]
def baseStart_2849388 : Nat := 118140960795 + 2849388 * 2 ^ 59
def prefixEnd_2849388 : Nat := 4983230072969 + 3 ^ 40 * 2849388 * 2
def baseEnd_2849388 : Nat := 1463105615153402990045909

theorem tailTrace_2849388 : CollatzResearch.WordTrace tailWord_2849388 prefixEnd_2849388 1463105615153402990045909 := by
  unfold tailWord_2849388
  simp only [CollatzResearch.WordTrace]
  refine ⟨51962859100580693786190409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69283812134107591714920545 51962859100580693786190409)
  ·
    refine ⟨38972144325435520339642807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51962859100580693786190409 38972144325435520339642807)
    ·
      refine ⟨58458216488153280509464211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38972144325435520339642807 58458216488153280509464211)
      ·
        refine ⟨87687324732229920764196317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58458216488153280509464211 87687324732229920764196317)
        ·
          refine ⟨32882746774586220286573619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 87687324732229920764196317 32882746774586220286573619)
          ·
            refine ⟨49324120161879330429860429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32882746774586220286573619 49324120161879330429860429)
            ·
              refine ⟨18496545060704748911197661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49324120161879330429860429 18496545060704748911197661)
              ·
                refine ⟨6936204397764280841699123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18496545060704748911197661 6936204397764280841699123)
                ·
                  refine ⟨10404306596646421262548685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6936204397764280841699123 10404306596646421262548685)
                  ·
                    refine ⟨3901614973742407973455757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10404306596646421262548685 3901614973742407973455757)
                    ·
                      refine ⟨1463105615153402990045909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3901614973742407973455757 1463105615153402990045909)
                      ·
                        rfl

theorem cell23_2849388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 3, 3].length) (baseStart_2849388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2849388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2849388 prefixEnd_2849388 := by exact prefixLift 2849388
  have htrace : WordTrace (prefixWord ++ tailWord_2849388) baseStart_2849388 baseEnd_2849388 := by
    simpa [prefixWord, tailWord_2849388, baseEnd_2849388] using wordTrace_append hprefix tailTrace_2849388
  have hstable : (prefixWord ++ tailWord_2849388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2849388).length < 2 ^ (prefixWord ++ tailWord_2849388).sum := by decide
  have hdescent : baseEnd_2849388 < baseStart_2849388 := by decide
  rcases family_descends (prefixWord ++ tailWord_2849388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2849481 : List Nat := [1, 2, 1, 1, 2, 1, 1, 1, 2, 11]
def baseStart_2849481 : Nat := 118140960795 + 2849481 * 2 ^ 59
def prefixEnd_2849481 : Nat := 4983230072969 + 3 ^ 40 * 2849481 * 2
def baseEnd_2849481 : Nat := 487717789618090375394327

theorem tailTrace_2849481 : CollatzResearch.WordTrace tailWord_2849481 prefixEnd_2849481 487717789618090375394327 := by
  unfold tailWord_2849481
  simp only [CollatzResearch.WordTrace]
  refine ⟨103929110189824464455516297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69286073459882976303677531 103929110189824464455516297)
  ·
    refine ⟨77946832642368348341637223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103929110189824464455516297 77946832642368348341637223)
    ·
      refine ⟨116920248963552522512455835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77946832642368348341637223 116920248963552522512455835)
      ·
        refine ⟨175380373445328783768683753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116920248963552522512455835 175380373445328783768683753)
        ·
          refine ⟨131535280083996587826512815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 175380373445328783768683753 131535280083996587826512815)
          ·
            refine ⟨197302920125994881739769223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 131535280083996587826512815 197302920125994881739769223)
            ·
              refine ⟨295954380188992322609653835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 197302920125994881739769223 295954380188992322609653835)
              ·
                refine ⟨443931570283488483914480753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 295954380188992322609653835 443931570283488483914480753)
                ·
                  refine ⟨332948677712616362935860565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 443931570283488483914480753 332948677712616362935860565)
                  ·
                    refine ⟨487717789618090375394327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 11 332948677712616362935860565 487717789618090375394327)
                    ·
                      rfl

theorem cell23_2849481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 1, 2, 11].length) (baseStart_2849481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2849481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2849481 prefixEnd_2849481 := by exact prefixLift 2849481
  have htrace : WordTrace (prefixWord ++ tailWord_2849481) baseStart_2849481 baseEnd_2849481 := by
    simpa [prefixWord, tailWord_2849481, baseEnd_2849481] using wordTrace_append hprefix tailTrace_2849481
  have hstable : (prefixWord ++ tailWord_2849481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2849481).length < 2 ^ (prefixWord ++ tailWord_2849481).sum := by decide
  have hdescent : baseEnd_2849481 < baseStart_2849481 := by decide
  rcases family_descends (prefixWord ++ tailWord_2849481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2849496 : List Nat := [2, 1, 2, 2, 3, 4, 2, 1, 2, 2, 2]
def baseStart_2849496 : Nat := 118140960795 + 2849496 * 2 ^ 59
def prefixEnd_2849496 : Nat := 4983230072969 + 3 ^ 40 * 2849496 * 2
def baseEnd_2849496 : Nat := 1463161071064088567495413

theorem tailTrace_2849496 : CollatzResearch.WordTrace tailWord_2849496 prefixEnd_2849496 1463161071064088567495413 := by
  unfold tailWord_2849496
  simp only [CollatzResearch.WordTrace]
  refine ⟨51964828642385061008656171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69286438189846748011541561 51964828642385061008656171)
  ·
    refine ⟨77947242963577591512984257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51964828642385061008656171 77947242963577591512984257)
    ·
      refine ⟨58460432222683193634738193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77947242963577591512984257 58460432222683193634738193)
      ·
        refine ⟨43845324167012395226053645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58460432222683193634738193 43845324167012395226053645)
        ·
          refine ⟨16441996562629648209770117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43845324167012395226053645 16441996562629648209770117)
          ·
            refine ⟨3082874355493059039331897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16441996562629648209770117 3082874355493059039331897)
            ·
              refine ⟨2312155766619794279498923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3082874355493059039331897 2312155766619794279498923)
              ·
                refine ⟨3468233649929691419248385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2312155766619794279498923 3468233649929691419248385)
                ·
                  refine ⟨2601175237447268564436289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3468233649929691419248385 2601175237447268564436289)
                  ·
                    refine ⟨1950881428085451423327217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2601175237447268564436289 1950881428085451423327217)
                    ·
                      refine ⟨1463161071064088567495413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1950881428085451423327217 1463161071064088567495413)
                      ·
                        rfl

theorem cell23_2849496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 4, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 4, 2, 1, 2, 2, 2].length) (baseStart_2849496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2849496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2849496 prefixEnd_2849496 := by exact prefixLift 2849496
  have htrace : WordTrace (prefixWord ++ tailWord_2849496) baseStart_2849496 baseEnd_2849496 := by
    simpa [prefixWord, tailWord_2849496, baseEnd_2849496] using wordTrace_append hprefix tailTrace_2849496
  have hstable : (prefixWord ++ tailWord_2849496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2849496).length < 2 ^ (prefixWord ++ tailWord_2849496).sum := by decide
  have hdescent : baseEnd_2849496 < baseStart_2849496 := by decide
  rcases family_descends (prefixWord ++ tailWord_2849496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2849498 : List Nat := [3, 1, 1, 2, 2, 2, 1, 2, 4, 5]
def baseStart_2849498 : Nat := 118140960795 + 2849498 * 2 ^ 59
def prefixEnd_2849498 : Nat := 4983230072969 + 3 ^ 40 * 2849498 * 2
def baseEnd_2849498 : Nat := 487720699341799186556801

theorem tailTrace_2849498 : CollatzResearch.WordTrace tailWord_2849498 prefixEnd_2849498 487720699341799186556801 := by
  unfold tailWord_2849498
  simp only [CollatzResearch.WordTrace]
  refine ⟨25982432557690719089721287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69286486820508584239256765 25982432557690719089721287)
  ·
    refine ⟨38973648836536078634581931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25982432557690719089721287 38973648836536078634581931)
    ·
      refine ⟨58460473254804117951872897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38973648836536078634581931 58460473254804117951872897)
      ·
        refine ⟨43845354941103088463904673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58460473254804117951872897 43845354941103088463904673)
        ·
          refine ⟨32884016205827316347928505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43845354941103088463904673 32884016205827316347928505)
          ·
            refine ⟨24663012154370487260946379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32884016205827316347928505 24663012154370487260946379)
            ·
              refine ⟨36994518231555730891419569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24663012154370487260946379 36994518231555730891419569)
              ·
                refine ⟨27745888673666798168564677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36994518231555730891419569 27745888673666798168564677)
                ·
                  refine ⟨5202354126312524656605877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27745888673666798168564677 5202354126312524656605877)
                  ·
                    refine ⟨487720699341799186556801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5202354126312524656605877 487720699341799186556801)
                    ·
                      rfl

theorem cell23_2849498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 2, 4, 5].length) (baseStart_2849498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2849498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2849498 prefixEnd_2849498 := by exact prefixLift 2849498
  have htrace : WordTrace (prefixWord ++ tailWord_2849498) baseStart_2849498 baseEnd_2849498 := by
    simpa [prefixWord, tailWord_2849498, baseEnd_2849498] using wordTrace_append hprefix tailTrace_2849498
  have hstable : (prefixWord ++ tailWord_2849498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2849498).length < 2 ^ (prefixWord ++ tailWord_2849498).sum := by decide
  have hdescent : baseEnd_2849498 < baseStart_2849498 := by decide
  rcases family_descends (prefixWord ++ tailWord_2849498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2849535 : List Nat := [1, 1, 2, 2, 1, 3, 1, 4, 2, 4, 2]
def baseStart_2849535 : Nat := 118140960795 + 2849535 * 2 ^ 59
def prefixEnd_2849535 : Nat := 4983230072969 + 3 ^ 40 * 2849535 * 2
def baseEnd_2849535 : Nat := 1463181096809613914907733

theorem tailTrace_2849535 : CollatzResearch.WordTrace tailWord_2849535 prefixEnd_2849535 1463181096809613914907733 := by
  unfold tailWord_2849535
  simp only [CollatzResearch.WordTrace]
  refine ⟨103931079731628831677982059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69287386487752554451988039 103931079731628831677982059)
  ·
    refine ⟨155896619597443247516973089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103931079731628831677982059 155896619597443247516973089)
    ·
      refine ⟨116922464698082435637729817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 155896619597443247516973089 116922464698082435637729817)
      ·
        refine ⟨87691848523561826728297363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 116922464698082435637729817 87691848523561826728297363)
        ·
          refine ⟨131537772785342740092446045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87691848523561826728297363 131537772785342740092446045)
          ·
            refine ⟨49326664794503527534667267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 131537772785342740092446045 49326664794503527534667267)
            ·
              refine ⟨73989997191755291302000901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49326664794503527534667267 73989997191755291302000901)
              ·
                refine ⟨13873124473454117119125169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 73989997191755291302000901 13873124473454117119125169)
                ·
                  refine ⟨10404843355090587839343877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13873124473454117119125169 10404843355090587839343877)
                  ·
                    refine ⟨1950908129079485219876977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10404843355090587839343877 1950908129079485219876977)
                    ·
                      refine ⟨1463181096809613914907733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1950908129079485219876977 1463181096809613914907733)
                      ·
                        rfl

theorem cell23_2849535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 4, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 4, 2, 4, 2].length) (baseStart_2849535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2849535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2849535 prefixEnd_2849535 := by exact prefixLift 2849535
  have htrace : WordTrace (prefixWord ++ tailWord_2849535) baseStart_2849535 baseEnd_2849535 := by
    simpa [prefixWord, tailWord_2849535, baseEnd_2849535] using wordTrace_append hprefix tailTrace_2849535
  have hstable : (prefixWord ++ tailWord_2849535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2849535).length < 2 ^ (prefixWord ++ tailWord_2849535).sum := by decide
  have hdescent : baseEnd_2849535 < baseStart_2849535 := by decide
  rcases family_descends (prefixWord ++ tailWord_2849535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2849548 : List Nat := [2, 2, 1, 2, 2, 1, 1, 2, 2, 4, 4]
def baseStart_2849548 : Nat := 118140960795 + 2849548 * 2 ^ 59
def prefixEnd_2849548 : Nat := 4983230072969 + 3 ^ 40 * 2849548 * 2
def baseEnd_2849548 : Nat := 1463187772058122364045173

theorem tailTrace_2849548 : CollatzResearch.WordTrace tailWord_2849548 prefixEnd_2849548 1463187772058122364045173 := by
  unfold tailWord_2849548
  simp only [CollatzResearch.WordTrace]
  refine ⟨51965776940290867449102649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69287702587054489932136865 51965776940290867449102649)
  ·
    refine ⟨38974332705218150586826987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51965776940290867449102649 38974332705218150586826987)
    ·
      refine ⟨58461499057827225880240481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38974332705218150586826987 58461499057827225880240481)
      ·
        refine ⟨43846124293370419410180361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58461499057827225880240481 43846124293370419410180361)
        ·
          refine ⟨32884593220027814557635271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43846124293370419410180361 32884593220027814557635271)
          ·
            refine ⟨49326889830041721836452907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32884593220027814557635271 49326889830041721836452907)
            ·
              refine ⟨73990334745062582754679361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49326889830041721836452907 73990334745062582754679361)
              ·
                refine ⟨55492751058796937066009521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 73990334745062582754679361 55492751058796937066009521)
                ·
                  refine ⟨41619563294097702799507141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 55492751058796937066009521 41619563294097702799507141)
                  ·
                    refine ⟨7803668117643319274907589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 41619563294097702799507141 7803668117643319274907589)
                    ·
                      refine ⟨1463187772058122364045173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7803668117643319274907589 1463187772058122364045173)
                      ·
                        rfl

theorem cell23_2849548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 2, 2, 4, 4].length) (baseStart_2849548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2849548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2849548 prefixEnd_2849548 := by exact prefixLift 2849548
  have htrace : WordTrace (prefixWord ++ tailWord_2849548) baseStart_2849548 baseEnd_2849548 := by
    simpa [prefixWord, tailWord_2849548, baseEnd_2849548] using wordTrace_append hprefix tailTrace_2849548
  have hstable : (prefixWord ++ tailWord_2849548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2849548).length < 2 ^ (prefixWord ++ tailWord_2849548).sum := by decide
  have hdescent : baseEnd_2849548 < baseStart_2849548 := by decide
  rcases family_descends (prefixWord ++ tailWord_2849548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2849572 : List Nat := [2, 3, 1, 3, 3, 1, 1, 1, 1, 4, 3]
def baseStart_2849572 : Nat := 118140960795 + 2849572 * 2 ^ 59
def prefixEnd_2849572 : Nat := 4983230072969 + 3 ^ 40 * 2849572 * 2
def baseEnd_2849572 : Nat := 1463200095593830270145063

theorem tailTrace_2849572 : CollatzResearch.WordTrace tailWord_2849572 prefixEnd_2849572 1463200095593830270145063 := by
  unfold tailWord_2849572
  simp only [CollatzResearch.WordTrace]
  refine ⟨51966214616247393498539485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69288286154996524664719313 51966214616247393498539485)
  ·
    refine ⟨19487330481092772561952307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51966214616247393498539485 19487330481092772561952307)
    ·
      refine ⟨29230995721639158842928461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19487330481092772561952307 29230995721639158842928461)
      ·
        refine ⟨10961623395614684566098173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29230995721639158842928461 10961623395614684566098173)
        ·
          refine ⟨4110608773355506712286815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10961623395614684566098173 4110608773355506712286815)
          ·
            refine ⟨6165913160033260068430223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4110608773355506712286815 6165913160033260068430223)
            ·
              refine ⟨9248869740049890102645335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6165913160033260068430223 9248869740049890102645335)
              ·
                refine ⟨13873304610074835153968003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9248869740049890102645335 13873304610074835153968003)
                ·
                  refine ⟨20809956915112252730952005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13873304610074835153968003 20809956915112252730952005)
                  ·
                    refine ⟨3901866921583547387053501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20809956915112252730952005 3901866921583547387053501)
                    ·
                      refine ⟨1463200095593830270145063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3901866921583547387053501 1463200095593830270145063)
                      ·
                        rfl

theorem cell23_2849572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 1, 1, 1, 4, 3].length) (baseStart_2849572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2849572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2849572 prefixEnd_2849572 := by exact prefixLift 2849572
  have htrace : WordTrace (prefixWord ++ tailWord_2849572) baseStart_2849572 baseEnd_2849572 := by
    simpa [prefixWord, tailWord_2849572, baseEnd_2849572] using wordTrace_append hprefix tailTrace_2849572
  have hstable : (prefixWord ++ tailWord_2849572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2849572).length < 2 ^ (prefixWord ++ tailWord_2849572).sum := by decide
  have hdescent : baseEnd_2849572 < baseStart_2849572 := by decide
  rcases family_descends (prefixWord ++ tailWord_2849572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2849612 : List Nat := [2, 2, 1, 3, 3, 1, 1, 2, 1, 5, 2]
def baseStart_2849612 : Nat := 118140960795 + 2849612 * 2 ^ 59
def prefixEnd_2849612 : Nat := 4983230072969 + 3 ^ 40 * 2849612 * 2
def baseEnd_2849612 : Nat := 1463220634820010113644879

theorem tailTrace_2849612 : CollatzResearch.WordTrace tailWord_2849612 prefixEnd_2849612 1463220634820010113644879 := by
  unfold tailWord_2849612
  simp only [CollatzResearch.WordTrace]
  refine ⟨51966944076174936914267545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69289258768233249219023393 51966944076174936914267545)
  ·
    refine ⟨38975208057131202685700659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51966944076174936914267545 38975208057131202685700659)
    ·
      refine ⟨58462812085696804028550989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38975208057131202685700659 58462812085696804028550989)
      ·
        refine ⟨21923554532136301510706621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58462812085696804028550989 21923554532136301510706621)
        ·
          refine ⟨8221332949551113066514983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21923554532136301510706621 8221332949551113066514983)
          ·
            refine ⟨12331999424326669599772475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8221332949551113066514983 12331999424326669599772475)
            ·
              refine ⟨18497999136490004399658713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12331999424326669599772475 18497999136490004399658713)
              ·
                refine ⟨13873499352367503299744035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18497999136490004399658713 13873499352367503299744035)
                ·
                  refine ⟨20810249028551254949616053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13873499352367503299744035 20810249028551254949616053)
                  ·
                    refine ⟨1950960846426680151526505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 20810249028551254949616053 1950960846426680151526505)
                    ·
                      refine ⟨1463220634820010113644879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1950960846426680151526505 1463220634820010113644879)
                      ·
                        rfl

theorem cell23_2849612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 1, 2, 1, 5, 2].length) (baseStart_2849612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2849612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2849612 prefixEnd_2849612 := by exact prefixLift 2849612
  have htrace : WordTrace (prefixWord ++ tailWord_2849612) baseStart_2849612 baseEnd_2849612 := by
    simpa [prefixWord, tailWord_2849612, baseEnd_2849612] using wordTrace_append hprefix tailTrace_2849612
  have hstable : (prefixWord ++ tailWord_2849612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2849612).length < 2 ^ (prefixWord ++ tailWord_2849612).sum := by decide
  have hdescent : baseEnd_2849612 < baseStart_2849612 := by decide
  rcases family_descends (prefixWord ++ tailWord_2849612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2849636 : List Nat := [2, 3, 1, 1, 4, 1, 3, 3, 1, 1, 3]
def baseStart_2849636 : Nat := 118140960795 + 2849636 * 2 ^ 59
def prefixEnd_2849636 : Nat := 4983230072969 + 3 ^ 40 * 2849636 * 2
def baseEnd_2849636 : Nat := 1463232958355718019744769

theorem tailTrace_2849636 : CollatzResearch.WordTrace tailWord_2849636 prefixEnd_2849636 1463232958355718019744769 := by
  unfold tailWord_2849636
  simp only [CollatzResearch.WordTrace]
  refine ⟨51967381752131462963704381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69289842336175283951605841 51967381752131462963704381)
  ·
    refine ⟨19487768157049298611389143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51967381752131462963704381 19487768157049298611389143)
    ·
      refine ⟨29231652235573947917083715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19487768157049298611389143 29231652235573947917083715)
      ·
        refine ⟨43847478353360921875625573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29231652235573947917083715 43847478353360921875625573)
        ·
          refine ⟨8221402191255172851679795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 43847478353360921875625573 8221402191255172851679795)
          ·
            refine ⟨12332103286882759277519693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8221402191255172851679795 12332103286882759277519693)
            ·
              refine ⟨4624538732581034729069885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12332103286882759277519693 4624538732581034729069885)
              ·
                refine ⟨1734202024717888023401207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4624538732581034729069885 1734202024717888023401207)
                ·
                  refine ⟨2601303037076832035101811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1734202024717888023401207 2601303037076832035101811)
                  ·
                    refine ⟨3901954555615248052652717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2601303037076832035101811 3901954555615248052652717)
                    ·
                      refine ⟨1463232958355718019744769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3901954555615248052652717 1463232958355718019744769)
                      ·
                        rfl

theorem cell23_2849636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 3, 3, 1, 1, 3].length) (baseStart_2849636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2849636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2849636 prefixEnd_2849636 := by exact prefixLift 2849636
  have htrace : WordTrace (prefixWord ++ tailWord_2849636) baseStart_2849636 baseEnd_2849636 := by
    simpa [prefixWord, tailWord_2849636, baseEnd_2849636] using wordTrace_append hprefix tailTrace_2849636
  have hstable : (prefixWord ++ tailWord_2849636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2849636).length < 2 ^ (prefixWord ++ tailWord_2849636).sum := by decide
  have hdescent : baseEnd_2849636 < baseStart_2849636 := by decide
  rcases family_descends (prefixWord ++ tailWord_2849636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2849646 : List Nat := [4, 1, 2, 3, 2, 1, 1, 2, 2, 3, 2]
def baseStart_2849646 : Nat := 118140960795 + 2849646 * 2 ^ 59
def prefixEnd_2849646 : Nat := 4983230072969 + 3 ^ 40 * 2849646 * 2
def baseEnd_2849646 : Nat := 1463238093162262980619723

theorem tailTrace_2849646 : CollatzResearch.WordTrace tailWord_2849646 prefixEnd_2849646 1463238093162262980619723 := by
  unfold tailWord_2849646
  simp only [CollatzResearch.WordTrace]
  refine ⟨12991891029278337204409099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 69290085489484465090181861 12991891029278337204409099)
  ·
    refine ⟨19487836543917505806613649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12991891029278337204409099 19487836543917505806613649)
    ·
      refine ⟨14615877407938129354960237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19487836543917505806613649 14615877407938129354960237)
      ·
        refine ⟨5480954027976798508110089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14615877407938129354960237 5480954027976798508110089)
        ·
          refine ⟨4110715520982598881082567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5480954027976798508110089 4110715520982598881082567)
          ·
            refine ⟨6166073281473898321623851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4110715520982598881082567 6166073281473898321623851)
            ·
              refine ⟨9249109922210847482435777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6166073281473898321623851 9249109922210847482435777)
              ·
                refine ⟨6936832441658135611826833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9249109922210847482435777 6936832441658135611826833)
                ·
                  refine ⟨5202624331243601708870125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6936832441658135611826833 5202624331243601708870125)
                  ·
                    refine ⟨1950984124216350640826297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5202624331243601708870125 1950984124216350640826297)
                    ·
                      refine ⟨1463238093162262980619723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1950984124216350640826297 1463238093162262980619723)
                      ·
                        rfl

theorem cell23_2849646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 1, 2, 2, 3, 2].length) (baseStart_2849646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2849646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2849646 prefixEnd_2849646 := by exact prefixLift 2849646
  have htrace : WordTrace (prefixWord ++ tailWord_2849646) baseStart_2849646 baseEnd_2849646 := by
    simpa [prefixWord, tailWord_2849646, baseEnd_2849646] using wordTrace_append hprefix tailTrace_2849646
  have hstable : (prefixWord ++ tailWord_2849646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2849646).length < 2 ^ (prefixWord ++ tailWord_2849646).sum := by decide
  have hdescent : baseEnd_2849646 < baseStart_2849646 := by decide
  rcases family_descends (prefixWord ++ tailWord_2849646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2849648 : List Nat := [2, 1, 1, 1, 4, 1, 13]
def baseStart_2849648 : Nat := 118140960795 + 2849648 * 2 ^ 59
def prefixEnd_2849648 : Nat := 4983230072969 + 3 ^ 40 * 2849648 * 2
def baseEnd_2849648 : Nat := 18064680495352740404873

theorem tailTrace_2849648 : CollatzResearch.WordTrace tailWord_2849648 prefixEnd_2849648 18064680495352740404873 := by
  unfold tailWord_2849648
  simp only [CollatzResearch.WordTrace]
  refine ⟨51967600590109725988422799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69290134120146301317897065 51967600590109725988422799)
  ·
    refine ⟨77951400885164588982634199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51967600590109725988422799 77951400885164588982634199)
    ·
      refine ⟨116927101327746883473951299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77951400885164588982634199 116927101327746883473951299)
      ·
        refine ⟨175390651991620325210926949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116927101327746883473951299 175390651991620325210926949)
        ·
          refine ⟨32885747248428810977048803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 175390651991620325210926949 32885747248428810977048803)
          ·
            refine ⟨49328620872643216465573205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32885747248428810977048803 49328620872643216465573205)
            ·
              refine ⟨18064680495352740404873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 13 49328620872643216465573205 18064680495352740404873)
              ·
                rfl

theorem cell23_2849648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 13].length) (baseStart_2849648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2849648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2849648 prefixEnd_2849648 := by exact prefixLift 2849648
  have htrace : WordTrace (prefixWord ++ tailWord_2849648) baseStart_2849648 baseEnd_2849648 := by
    simpa [prefixWord, tailWord_2849648, baseEnd_2849648] using wordTrace_append hprefix tailTrace_2849648
  have hstable : (prefixWord ++ tailWord_2849648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2849648).length < 2 ^ (prefixWord ++ tailWord_2849648).sum := by decide
  have hdescent : baseEnd_2849648 < baseStart_2849648 := by decide
  rcases family_descends (prefixWord ++ tailWord_2849648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2849653 : List Nat := [1, 3, 4, 1, 1, 3, 3, 2, 1, 1, 3]
def baseStart_2849653 : Nat := 118140960795 + 2849653 * 2 ^ 59
def prefixEnd_2849653 : Nat := 4983230072969 + 3 ^ 40 * 2849653 * 2
def baseEnd_2849653 : Nat := 1463241687526844453232191

theorem tailTrace_2849653 : CollatzResearch.WordTrace tailWord_2849653 prefixEnd_2849653 1463241687526844453232191 := by
  unfold tailWord_2849653
  simp only [CollatzResearch.WordTrace]
  refine ⟨103935383545201337830777613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69290255696800891887185075 103935383545201337830777613)
  ·
    refine ⟨38975768829450501686541605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 103935383545201337830777613 38975768829450501686541605)
    ·
      refine ⟨7307956655521969066226551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 38975768829450501686541605 7307956655521969066226551)
      ·
        refine ⟨10961934983282953599339827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7307956655521969066226551 10961934983282953599339827)
        ·
          refine ⟨16442902474924430399009741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10961934983282953599339827 16442902474924430399009741)
          ·
            refine ⟨6166088428096661399628653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16442902474924430399009741 6166088428096661399628653)
            ·
              refine ⟨2312283160536248024860745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6166088428096661399628653 2312283160536248024860745)
              ·
                refine ⟨1734212370402186018645559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2312283160536248024860745 1734212370402186018645559)
                ·
                  refine ⟨2601318555603279027968339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1734212370402186018645559 2601318555603279027968339)
                  ·
                    refine ⟨3901977833404918541952509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2601318555603279027968339 3901977833404918541952509)
                    ·
                      refine ⟨1463241687526844453232191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3901977833404918541952509 1463241687526844453232191)
                      ·
                        rfl

theorem cell23_2849653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 3, 2, 1, 1, 3].length) (baseStart_2849653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2849653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2849653 prefixEnd_2849653 := by exact prefixLift 2849653
  have htrace : WordTrace (prefixWord ++ tailWord_2849653) baseStart_2849653 baseEnd_2849653 := by
    simpa [prefixWord, tailWord_2849653, baseEnd_2849653] using wordTrace_append hprefix tailTrace_2849653
  have hstable : (prefixWord ++ tailWord_2849653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2849653).length < 2 ^ (prefixWord ++ tailWord_2849653).sum := by decide
  have hdescent : baseEnd_2849653 < baseStart_2849653 := by decide
  rcases family_descends (prefixWord ++ tailWord_2849653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2849659 : List Nat := [1, 1, 1, 1, 1, 5, 5, 1, 3, 2, 2]
def baseStart_2849659 : Nat := 118140960795 + 2849659 * 2 ^ 59
def prefixEnd_2849659 : Nat := 4983230072969 + 3 ^ 40 * 2849659 * 2
def baseEnd_2849659 : Nat := 1463244768410771429757163

theorem tailTrace_2849659 : CollatzResearch.WordTrace tailWord_2849659 prefixEnd_2849659 1463244768410771429757163 := by
  unfold tailWord_2849659
  simp only [CollatzResearch.WordTrace]
  refine ⟨103935602383179600855496031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69290401588786400570330687 103935602383179600855496031)
  ·
    refine ⟨155903403574769401283244047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103935602383179600855496031 155903403574769401283244047)
    ·
      refine ⟨233855105362154101924866071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155903403574769401283244047 233855105362154101924866071)
      ·
        refine ⟨350782658043231152887299107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 233855105362154101924866071 350782658043231152887299107)
        ·
          refine ⟨526173987064846729330948661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 350782658043231152887299107 526173987064846729330948661)
          ·
            refine ⟨49328811287329380874776437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 526173987064846729330948661 49328811287329380874776437)
            ·
              refine ⟨4624576058187129457010291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 49328811287329380874776437 4624576058187129457010291)
              ·
                refine ⟨6936864087280694185515437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4624576058187129457010291 6936864087280694185515437)
                ·
                  refine ⟨2601324032730260319568289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6936864087280694185515437 2601324032730260319568289)
                  ·
                    refine ⟨1950993024547695239676217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2601324032730260319568289 1950993024547695239676217)
                    ·
                      refine ⟨1463244768410771429757163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1950993024547695239676217 1463244768410771429757163)
                      ·
                        rfl

theorem cell23_2849659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 5, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 5, 1, 3, 2, 2].length) (baseStart_2849659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2849659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2849659 prefixEnd_2849659 := by exact prefixLift 2849659
  have htrace : WordTrace (prefixWord ++ tailWord_2849659) baseStart_2849659 baseEnd_2849659 := by
    simpa [prefixWord, tailWord_2849659, baseEnd_2849659] using wordTrace_append hprefix tailTrace_2849659
  have hstable : (prefixWord ++ tailWord_2849659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2849659).length < 2 ^ (prefixWord ++ tailWord_2849659).sum := by decide
  have hdescent : baseEnd_2849659 < baseStart_2849659 := by decide
  rcases family_descends (prefixWord ++ tailWord_2849659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2849669 : List Nat := [1, 3, 1, 1, 3, 3, 4, 1, 2, 4]
def baseStart_2849669 : Nat := 118140960795 + 2849669 * 2 ^ 59
def prefixEnd_2849669 : Nat := 4983230072969 + 3 ^ 40 * 2849669 * 2
def baseEnd_2849669 : Nat := 487749967739105463544039

theorem tailTrace_2849669 : CollatzResearch.WordTrace tailWord_2849669 prefixEnd_2849669 487749967739105463544039 := by
  unfold tailWord_2849669
  simp only [CollatzResearch.WordTrace]
  refine ⟨103935967113143372563360061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69290644742095581708906707 103935967113143372563360061)
  ·
    refine ⟨38975987667428764711260023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 103935967113143372563360061 38975987667428764711260023)
    ·
      refine ⟨58463981501143147066890035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38975987667428764711260023 58463981501143147066890035)
      ·
        refine ⟨87695972251714720600335053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58463981501143147066890035 87695972251714720600335053)
        ·
          refine ⟨32885989594393020225125645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 87695972251714720600335053 32885989594393020225125645)
          ·
            refine ⟨12332246097897382584422117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32885989594393020225125645 12332246097897382584422117)
            ·
              refine ⟨2312296143355759234579147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12332246097897382584422117 2312296143355759234579147)
              ·
                refine ⟨3468444215033638851868721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2312296143355759234579147 3468444215033638851868721)
                ·
                  refine ⟨2601333161275229138901541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3468444215033638851868721 2601333161275229138901541)
                  ·
                    refine ⟨487749967739105463544039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2601333161275229138901541 487749967739105463544039)
                    ·
                      rfl

theorem cell23_2849669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 4, 1, 2, 4].length) (baseStart_2849669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2849669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2849669 prefixEnd_2849669 := by exact prefixLift 2849669
  have htrace : WordTrace (prefixWord ++ tailWord_2849669) baseStart_2849669 baseEnd_2849669 := by
    simpa [prefixWord, tailWord_2849669, baseEnd_2849669] using wordTrace_append hprefix tailTrace_2849669
  have hstable : (prefixWord ++ tailWord_2849669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2849669).length < 2 ^ (prefixWord ++ tailWord_2849669).sum := by decide
  have hdescent : baseEnd_2849669 < baseStart_2849669 := by decide
  rcases family_descends (prefixWord ++ tailWord_2849669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2849686 : List Nat := [5, 3, 1, 1, 1, 2, 1, 2, 1, 6]
def baseStart_2849686 : Nat := 118140960795 + 2849686 * 2 ^ 59
def prefixEnd_2849686 : Nat := 4983230072969 + 3 ^ 40 * 2849686 * 2
def baseEnd_2849686 : Nat := 487752877462814274706513

theorem tailTrace_2849686 : CollatzResearch.WordTrace tailWord_2849686 prefixEnd_2849686 487752877462814274706513 := by
  unfold tailWord_2849686
  simp only [CollatzResearch.WordTrace]
  refine ⟨6496036697130111529170557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 69291058102721189644485941 6496036697130111529170557)
  ·
    refine ⟨2436013761423791823438959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6496036697130111529170557 2436013761423791823438959)
    ·
      refine ⟨3654020642135687735158439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2436013761423791823438959 3654020642135687735158439)
      ·
        refine ⟨5481030963203531602737659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3654020642135687735158439 5481030963203531602737659)
        ·
          refine ⟨8221546444805297404106489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5481030963203531602737659 8221546444805297404106489)
          ·
            refine ⟨6166159833603973053079867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8221546444805297404106489 6166159833603973053079867)
            ·
              refine ⟨9249239750405959579619801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6166159833603973053079867 9249239750405959579619801)
              ·
                refine ⟨6936929812804469684714851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9249239750405959579619801 6936929812804469684714851)
                ·
                  refine ⟨10405394719206704527072277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6936929812804469684714851 10405394719206704527072277)
                  ·
                    refine ⟨487752877462814274706513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10405394719206704527072277 487752877462814274706513)
                    ·
                      rfl

theorem cell23_2849686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 1, 2, 1, 6].length) (baseStart_2849686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2849686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2849686 prefixEnd_2849686 := by exact prefixLift 2849686
  have htrace : WordTrace (prefixWord ++ tailWord_2849686) baseStart_2849686 baseEnd_2849686 := by
    simpa [prefixWord, tailWord_2849686, baseEnd_2849686] using wordTrace_append hprefix tailTrace_2849686
  have hstable : (prefixWord ++ tailWord_2849686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2849686).length < 2 ^ (prefixWord ++ tailWord_2849686).sum := by decide
  have hdescent : baseEnd_2849686 < baseStart_2849686 := by decide
  rcases family_descends (prefixWord ++ tailWord_2849686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2849735 : List Nat := [1, 1, 4, 1, 1, 2, 2, 1, 4, 1, 5]
def baseStart_2849735 : Nat := 118140960795 + 2849735 * 2 ^ 59
def prefixEnd_2849735 : Nat := 4983230072969 + 3 ^ 40 * 2849735 * 2
def baseEnd_2849735 : Nat := 1463283792940513132406813

theorem tailTrace_2849735 : CollatzResearch.WordTrace tailWord_2849735 prefixEnd_2849735 1463283792940513132406813 := by
  unfold tailWord_2849735
  simp only [CollatzResearch.WordTrace]
  refine ⟨103938374330904265835262659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69292249553936177223508439 103938374330904265835262659)
  ·
    refine ⟨155907561496356398752893989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103938374330904265835262659 155907561496356398752893989)
    ·
      refine ⟨29232667780566824766167623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 155907561496356398752893989 29232667780566824766167623)
      ·
        refine ⟨43849001670850237149251435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29232667780566824766167623 43849001670850237149251435)
        ·
          refine ⟨65773502506275355723877153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43849001670850237149251435 65773502506275355723877153)
          ·
            refine ⟨49330126879706516792907865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65773502506275355723877153 49330126879706516792907865)
            ·
              refine ⟨36997595159779887594680899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49330126879706516792907865 36997595159779887594680899)
              ·
                refine ⟨55496392739669831392021349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36997595159779887594680899 55496392739669831392021349)
                ·
                  refine ⟨10405573638688093386004003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 55496392739669831392021349 10405573638688093386004003)
                  ·
                    refine ⟨15608360458032140079006005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10405573638688093386004003 15608360458032140079006005)
                    ·
                      refine ⟨1463283792940513132406813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15608360458032140079006005 1463283792940513132406813)
                      ·
                        rfl

theorem cell23_2849735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 1, 4, 1, 5].length) (baseStart_2849735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2849735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2849735 prefixEnd_2849735 := by exact prefixLift 2849735
  have htrace : WordTrace (prefixWord ++ tailWord_2849735) baseStart_2849735 baseEnd_2849735 := by
    simpa [prefixWord, tailWord_2849735, baseEnd_2849735] using wordTrace_append hprefix tailTrace_2849735
  have hstable : (prefixWord ++ tailWord_2849735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2849735).length < 2 ^ (prefixWord ++ tailWord_2849735).sum := by decide
  have hdescent : baseEnd_2849735 < baseStart_2849735 := by decide
  rcases family_descends (prefixWord ++ tailWord_2849735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2849745 : List Nat := [1, 2, 2, 1, 2, 1, 3, 2, 1, 4, 4]
def baseStart_2849745 : Nat := 118140960795 + 2849745 * 2 ^ 59
def prefixEnd_2849745 : Nat := 4983230072969 + 3 ^ 40 * 2849745 * 2
def baseEnd_2849745 : Nat := 1463288927747058093281767

theorem tailTrace_2849745 : CollatzResearch.WordTrace tailWord_2849745 prefixEnd_2849745 1463288927747058093281767 := by
  unfold tailWord_2849745
  simp only [CollatzResearch.WordTrace]
  refine ⟨103938739060868037543126689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69292492707245358362084459 103938739060868037543126689)
  ·
    refine ⟨77954054295651028157345017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103938739060868037543126689 77954054295651028157345017)
    ·
      refine ⟨58465540721738271118008763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77954054295651028157345017 58465540721738271118008763)
      ·
        refine ⟨87698311082607406677013145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58465540721738271118008763 87698311082607406677013145)
        ·
          refine ⟨65773733311955555007759859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87698311082607406677013145 65773733311955555007759859)
          ·
            refine ⟨98660599967933332511639789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65773733311955555007759859 98660599967933332511639789)
            ·
              refine ⟨36997724987974999691864921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 98660599967933332511639789 36997724987974999691864921)
              ·
                refine ⟨27748293740981249768898691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36997724987974999691864921 27748293740981249768898691)
                ·
                  refine ⟨41622440611471874653348037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27748293740981249768898691 41622440611471874653348037)
                  ·
                    refine ⟨7804207614650976497502757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 41622440611471874653348037 7804207614650976497502757)
                    ·
                      refine ⟨1463288927747058093281767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7804207614650976497502757 1463288927747058093281767)
                      ·
                        rfl

theorem cell23_2849745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 2, 1, 4, 4].length) (baseStart_2849745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2849745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2849745 prefixEnd_2849745 := by exact prefixLift 2849745
  have htrace : WordTrace (prefixWord ++ tailWord_2849745) baseStart_2849745 baseEnd_2849745 := by
    simpa [prefixWord, tailWord_2849745, baseEnd_2849745] using wordTrace_append hprefix tailTrace_2849745
  have hstable : (prefixWord ++ tailWord_2849745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2849745).length < 2 ^ (prefixWord ++ tailWord_2849745).sum := by decide
  have hdescent : baseEnd_2849745 < baseStart_2849745 := by decide
  rcases family_descends (prefixWord ++ tailWord_2849745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2849753 : List Nat := [1, 2, 1, 2, 5, 3, 2, 1, 1, 3, 2]
def baseStart_2849753 : Nat := 118140960795 + 2849753 * 2 ^ 59
def prefixEnd_2849753 : Nat := 4983230072969 + 3 ^ 40 * 2849753 * 2
def baseEnd_2849753 : Nat := 1463293035592294061981731

theorem tailTrace_2849753 : CollatzResearch.WordTrace tailWord_2849753 prefixEnd_2849753 1463293035592294061981731 := by
  unfold tailWord_2849753
  simp only [CollatzResearch.WordTrace]
  refine ⟨103939030844839054909417913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69292687229892703272945275 103939030844839054909417913)
  ·
    refine ⟨77954273133629291182063435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103939030844839054909417913 77954273133629291182063435)
    ·
      refine ⟨116931409700443936773095153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77954273133629291182063435 116931409700443936773095153)
      ·
        refine ⟨87698557275332952579821365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 116931409700443936773095153 87698557275332952579821365)
        ·
          refine ⟨8221739744562464304358253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 87698557275332952579821365 8221739744562464304358253)
          ·
            refine ⟨3083152404210924114134345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8221739744562464304358253 3083152404210924114134345)
            ·
              refine ⟨2312364303158193085600759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3083152404210924114134345 2312364303158193085600759)
              ·
                refine ⟨3468546454737289628401139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2312364303158193085600759 3468546454737289628401139)
                ·
                  refine ⟨5202819682105934442601709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3468546454737289628401139 5202819682105934442601709)
                  ·
                    refine ⟨1951057380789725415975641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5202819682105934442601709 1951057380789725415975641)
                    ·
                      refine ⟨1463293035592294061981731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1951057380789725415975641 1463293035592294061981731)
                      ·
                        rfl

theorem cell23_2849753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 3, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 3, 2, 1, 1, 3, 2].length) (baseStart_2849753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2849753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2849753 prefixEnd_2849753 := by exact prefixLift 2849753
  have htrace : WordTrace (prefixWord ++ tailWord_2849753) baseStart_2849753 baseEnd_2849753 := by
    simpa [prefixWord, tailWord_2849753, baseEnd_2849753] using wordTrace_append hprefix tailTrace_2849753
  have hstable : (prefixWord ++ tailWord_2849753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2849753).length < 2 ^ (prefixWord ++ tailWord_2849753).sum := by decide
  have hdescent : baseEnd_2849753 < baseStart_2849753 := by decide
  rcases family_descends (prefixWord ++ tailWord_2849753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2849785 : List Nat := [1, 2, 1, 3, 1, 3, 1, 1, 3, 7]
def baseStart_2849785 : Nat := 118140960795 + 2849785 * 2 ^ 59
def prefixEnd_2849785 : Nat := 4983230072969 + 3 ^ 40 * 2849785 * 2
def baseEnd_2849785 : Nat := 487769822324412645593861

theorem tailTrace_2849785 : CollatzResearch.WordTrace tailWord_2849785 prefixEnd_2849785 487769822324412645593861 := by
  unfold tailWord_2849785
  simp only [CollatzResearch.WordTrace]
  refine ⟨103940197980723124374582809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69293465320482082916388539 103940197980723124374582809)
  ·
    refine ⟨77955148485542343280937107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103940197980723124374582809 77955148485542343280937107)
    ·
      refine ⟨116932722728313514921405661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77955148485542343280937107 116932722728313514921405661)
      ·
        refine ⟨43849771023117568095527123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 116932722728313514921405661 43849771023117568095527123)
        ·
          refine ⟨65774656534676352143290685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43849771023117568095527123 65774656534676352143290685)
          ·
            refine ⟨24665496200503632053734007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 65774656534676352143290685 24665496200503632053734007)
            ·
              refine ⟨36998244300755448080601011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24665496200503632053734007 36998244300755448080601011)
              ·
                refine ⟨55497366451133172120901517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36998244300755448080601011 55497366451133172120901517)
                ·
                  refine ⟨20811512419174939545338069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 55497366451133172120901517 20811512419174939545338069)
                  ·
                    refine ⟨487769822324412645593861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 20811512419174939545338069 487769822324412645593861)
                    ·
                      rfl

theorem cell23_2849785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 1, 3, 7].length) (baseStart_2849785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2849785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2849785 prefixEnd_2849785 := by exact prefixLift 2849785
  have htrace : WordTrace (prefixWord ++ tailWord_2849785) baseStart_2849785 baseEnd_2849785 := by
    simpa [prefixWord, tailWord_2849785, baseEnd_2849785] using wordTrace_append hprefix tailTrace_2849785
  have hstable : (prefixWord ++ tailWord_2849785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2849785).length < 2 ^ (prefixWord ++ tailWord_2849785).sum := by decide
  have hdescent : baseEnd_2849785 < baseStart_2849785 := by decide
  rcases family_descends (prefixWord ++ tailWord_2849785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2849792 : List Nat := [2, 1, 1, 2, 1, 1, 1, 2, 3, 7, 2]
def baseStart_2849792 : Nat := 118140960795 + 2849792 * 2 ^ 59
def prefixEnd_2849792 : Nat := 4983230072969 + 3 ^ 40 * 2849792 * 2
def baseEnd_2849792 : Nat := 1463313061337819409394051

theorem tailTrace_2849792 : CollatzResearch.WordTrace tailWord_2849792 prefixEnd_2849792 1463313061337819409394051 := by
  unfold tailWord_2849792
  simp only [CollatzResearch.WordTrace]
  refine ⟨51970226645848882285043815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69293635527798509713391753 51970226645848882285043815)
  ·
    refine ⟨77955339968773323427565723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51970226645848882285043815 77955339968773323427565723)
    ·
      refine ⟨116933009953159985141348585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77955339968773323427565723 116933009953159985141348585)
      ·
        refine ⟨87699757464869988856011439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 116933009953159985141348585 87699757464869988856011439)
        ·
          refine ⟨131549636197304983284017159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87699757464869988856011439 131549636197304983284017159)
          ·
            refine ⟨197324454295957474926025739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 131549636197304983284017159 197324454295957474926025739)
            ·
              refine ⟨295986681443936212389038609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 197324454295957474926025739 295986681443936212389038609)
              ·
                refine ⟨221990011082952159291778957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 295986681443936212389038609 221990011082952159291778957)
                ·
                  refine ⟨83246254156107059734417109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 221990011082952159291778957 83246254156107059734417109)
                  ·
                    refine ⟨1951084081783759212525401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 83246254156107059734417109 1951084081783759212525401)
                    ·
                      refine ⟨1463313061337819409394051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1951084081783759212525401 1463313061337819409394051)
                      ·
                        rfl

theorem cell23_2849792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 2, 3, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 2, 3, 7, 2].length) (baseStart_2849792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2849792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2849792 prefixEnd_2849792 := by exact prefixLift 2849792
  have htrace : WordTrace (prefixWord ++ tailWord_2849792) baseStart_2849792 baseEnd_2849792 := by
    simpa [prefixWord, tailWord_2849792, baseEnd_2849792] using wordTrace_append hprefix tailTrace_2849792
  have hstable : (prefixWord ++ tailWord_2849792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2849792).length < 2 ^ (prefixWord ++ tailWord_2849792).sum := by decide
  have hdescent : baseEnd_2849792 < baseStart_2849792 := by decide
  rcases family_descends (prefixWord ++ tailWord_2849792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2849795 : List Nat := [1, 1, 1, 3, 2, 1, 1, 1, 5, 2, 5]
def baseStart_2849795 : Nat := 118140960795 + 2849795 * 2 ^ 59
def prefixEnd_2849795 : Nat := 4983230072969 + 3 ^ 40 * 2849795 * 2
def baseEnd_2849795 : Nat := 1463314601779782897656537

theorem tailTrace_2849795 : CollatzResearch.WordTrace tailWord_2849795 prefixEnd_2849795 1463314601779782897656537 := by
  unfold tailWord_2849795
  simp only [CollatzResearch.WordTrace]
  refine ⟨103940562710686896082446839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69293708473791264054964559 103940562710686896082446839)
  ·
    refine ⟨155910844066030344123670259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103940562710686896082446839 155910844066030344123670259)
    ·
      refine ⟨233866266099045516185505389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155910844066030344123670259 233866266099045516185505389)
      ·
        refine ⟨87699849787142068569564521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 233866266099045516185505389 87699849787142068569564521)
        ·
          refine ⟨65774887340356551427173391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87699849787142068569564521 65774887340356551427173391)
          ·
            refine ⟨98662331010534827140760087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65774887340356551427173391 98662331010534827140760087)
            ·
              refine ⟨147993496515802240711140131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 98662331010534827140760087 147993496515802240711140131)
              ·
                refine ⟨221990244773703361066710197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 147993496515802240711140131 221990244773703361066710197)
                ·
                  refine ⟨20811585447534690100004081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 221990244773703361066710197 20811585447534690100004081)
                  ·
                    refine ⟨15608689085651017575003061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20811585447534690100004081 15608689085651017575003061)
                    ·
                      refine ⟨1463314601779782897656537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15608689085651017575003061 1463314601779782897656537)
                      ·
                        rfl

theorem cell23_2849795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 1, 5, 2, 5].length) (baseStart_2849795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2849795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2849795 prefixEnd_2849795 := by exact prefixLift 2849795
  have htrace : WordTrace (prefixWord ++ tailWord_2849795) baseStart_2849795 baseEnd_2849795 := by
    simpa [prefixWord, tailWord_2849795, baseEnd_2849795] using wordTrace_append hprefix tailTrace_2849795
  have hstable : (prefixWord ++ tailWord_2849795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2849795).length < 2 ^ (prefixWord ++ tailWord_2849795).sum := by decide
  have hdescent : baseEnd_2849795 < baseStart_2849795 := by decide
  rcases family_descends (prefixWord ++ tailWord_2849795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2849802 : List Nat := [3, 1, 2, 2, 3, 1, 2, 1, 1, 7]
def baseStart_2849802 : Nat := 118140960795 + 2849802 * 2 ^ 59
def prefixEnd_2849802 : Nat := 4983230072969 + 3 ^ 40 * 2849802 * 2
def baseEnd_2849802 : Nat := 487772732048121456756335

theorem tailTrace_2849802 : CollatzResearch.WordTrace tailWord_2849802 prefixEnd_2849802 487772732048121456756335 := by
  unfold tailWord_2849802
  simp only [CollatzResearch.WordTrace]
  refine ⟨25985204505415384069487915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69293878681107690851967773 25985204505415384069487915)
  ·
    refine ⟨38977806758123076104231873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25985204505415384069487915 38977806758123076104231873)
    ·
      refine ⟨29233355068592307078173905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38977806758123076104231873 29233355068592307078173905)
      ·
        refine ⟨21925016301444230308630429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29233355068592307078173905 21925016301444230308630429)
        ·
          refine ⟨8221881113041586365736411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21925016301444230308630429 8221881113041586365736411)
          ·
            refine ⟨12332821669562379548604617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8221881113041586365736411 12332821669562379548604617)
            ·
              refine ⟨9249616252171784661453463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12332821669562379548604617 9249616252171784661453463)
              ·
                refine ⟨13874424378257676992180195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9249616252171784661453463 13874424378257676992180195)
                ·
                  refine ⟨20811636567386515488270293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13874424378257676992180195 20811636567386515488270293)
                  ·
                    refine ⟨487772732048121456756335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 20811636567386515488270293 487772732048121456756335)
                    ·
                      rfl

theorem cell23_2849802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 2, 1, 1, 7].length) (baseStart_2849802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2849802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2849802 prefixEnd_2849802 := by exact prefixLift 2849802
  have htrace : WordTrace (prefixWord ++ tailWord_2849802) baseStart_2849802 baseEnd_2849802 := by
    simpa [prefixWord, tailWord_2849802, baseEnd_2849802] using wordTrace_append hprefix tailTrace_2849802
  have hstable : (prefixWord ++ tailWord_2849802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2849802).length < 2 ^ (prefixWord ++ tailWord_2849802).sum := by decide
  have hdescent : baseEnd_2849802 < baseStart_2849802 := by decide
  rcases family_descends (prefixWord ++ tailWord_2849802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2849806 : List Nat := [4, 1, 1, 2, 2, 4, 1, 3, 5]
def baseStart_2849806 : Nat := 118140960795 + 2849806 * 2 ^ 59
def prefixEnd_2849806 : Nat := 4983230072969 + 3 ^ 40 * 2849806 * 2
def baseEnd_2849806 : Nat := 162591138896331372735443

theorem tailTrace_2849806 : CollatzResearch.WordTrace tailWord_2849806 prefixEnd_2849806 162591138896331372735443 := by
  unfold tailWord_2849806
  simp only [CollatzResearch.WordTrace]
  refine ⟨12992620489205880620137159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 69293975942431363307398181 12992620489205880620137159)
  ·
    refine ⟨19488930733808820930205739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12992620489205880620137159 19488930733808820930205739)
    ·
      refine ⟨29233396100713231395308609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19488930733808820930205739 29233396100713231395308609)
      ·
        refine ⟨21925047075534923546481457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29233396100713231395308609 21925047075534923546481457)
        ·
          refine ⟨16443785306651192659861093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21925047075534923546481457 16443785306651192659861093)
          ·
            refine ⟨3083209744997098623723955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16443785306651192659861093 3083209744997098623723955)
            ·
              refine ⟨4624814617495647935585933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3083209744997098623723955 4624814617495647935585933)
              ·
                refine ⟨1734305481560867975844725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4624814617495647935585933 1734305481560867975844725)
                ·
                  refine ⟨162591138896331372735443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1734305481560867975844725 162591138896331372735443)
                  ·
                    rfl

theorem cell23_2849806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 4, 1, 3, 5].length) (baseStart_2849806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2849806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2849806 prefixEnd_2849806 := by exact prefixLift 2849806
  have htrace : WordTrace (prefixWord ++ tailWord_2849806) baseStart_2849806 baseEnd_2849806 := by
    simpa [prefixWord, tailWord_2849806, baseEnd_2849806] using wordTrace_append hprefix tailTrace_2849806
  have hstable : (prefixWord ++ tailWord_2849806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2849806).length < 2 ^ (prefixWord ++ tailWord_2849806).sum := by decide
  have hdescent : baseEnd_2849806 < baseStart_2849806 := by decide
  rcases family_descends (prefixWord ++ tailWord_2849806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2849859 : List Nat := [1, 1, 1, 3, 1, 2, 6, 1, 2, 2, 3]
def baseStart_2849859 : Nat := 118140960795 + 2849859 * 2 ^ 59
def prefixEnd_2849859 : Nat := 4983230072969 + 3 ^ 40 * 2849859 * 2
def baseEnd_2849859 : Nat := 1463347464541670647256243

theorem tailTrace_2849859 : CollatzResearch.WordTrace tailWord_2849859 prefixEnd_2849859 1463347464541670647256243 := by
  unfold tailWord_2849859
  simp only [CollatzResearch.WordTrace]
  refine ⟨103942896982455035012776631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69295264654970023341851087 103942896982455035012776631)
  ·
    refine ⟨155914345473682552519164947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103942896982455035012776631 155914345473682552519164947)
    ·
      refine ⟨233871518210523828778747421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155914345473682552519164947 233871518210523828778747421)
      ·
        refine ⟨87701819328946435792030283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 233871518210523828778747421 87701819328946435792030283)
        ·
          refine ⟨131552728993419653688045425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87701819328946435792030283 131552728993419653688045425)
          ·
            refine ⟨98664546745064740266034069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 131552728993419653688045425 98664546745064740266034069)
            ·
              refine ⟨4624900628674909699970347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 98664546745064740266034069 4624900628674909699970347)
              ·
                refine ⟨6937350943012364549955521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4624900628674909699970347 6937350943012364549955521)
                ·
                  refine ⟨5203013207259273412466641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6937350943012364549955521 5203013207259273412466641)
                  ·
                    refine ⟨3902259905444455059349981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5203013207259273412466641 3902259905444455059349981)
                    ·
                      refine ⟨1463347464541670647256243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3902259905444455059349981 1463347464541670647256243)
                      ·
                        rfl

theorem cell23_2849859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 6, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 6, 1, 2, 2, 3].length) (baseStart_2849859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2849859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2849859 prefixEnd_2849859 := by exact prefixLift 2849859
  have htrace : WordTrace (prefixWord ++ tailWord_2849859) baseStart_2849859 baseEnd_2849859 := by
    simpa [prefixWord, tailWord_2849859, baseEnd_2849859] using wordTrace_append hprefix tailTrace_2849859
  have hstable : (prefixWord ++ tailWord_2849859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2849859).length < 2 ^ (prefixWord ++ tailWord_2849859).sum := by decide
  have hdescent : baseEnd_2849859 < baseStart_2849859 := by decide
  rcases family_descends (prefixWord ++ tailWord_2849859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2849906 : List Nat := [3, 2, 1, 2, 2, 1, 3, 2, 3, 1, 3]
def baseStart_2849906 : Nat := 118140960795 + 2849906 * 2 ^ 59
def prefixEnd_2849906 : Nat := 4983230072969 + 3 ^ 40 * 2849906 * 2
def baseEnd_2849906 : Nat := 1463371598132431963368527

theorem tailTrace_2849906 : CollatzResearch.WordTrace tailWord_2849906 prefixEnd_2849906 1463371598132431963368527 := by
  unfold tailWord_2849906
  simp only [CollatzResearch.WordTrace]
  refine ⟨25986152803321190509934393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69296407475523174693158381 25986152803321190509934393)
  ·
    refine ⟨19489614602490892882450795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25986152803321190509934393 19489614602490892882450795)
    ·
      refine ⟨29234421903736339323676193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19489614602490892882450795 29234421903736339323676193)
      ·
        refine ⟨21925816427802254492757145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29234421903736339323676193 21925816427802254492757145)
        ·
          refine ⟨16444362320851690869567859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21925816427802254492757145 16444362320851690869567859)
          ·
            refine ⟨24666543481277536304351789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16444362320851690869567859 24666543481277536304351789)
            ·
              refine ⟨9249953805479076114131921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24666543481277536304351789 9249953805479076114131921)
              ·
                refine ⟨6937465354109307085598941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9249953805479076114131921 6937465354109307085598941)
                ·
                  refine ⟨2601549507790990157099603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6937465354109307085598941 2601549507790990157099603)
                  ·
                    refine ⟨3902324261686485235649405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2601549507790990157099603 3902324261686485235649405)
                    ·
                      refine ⟨1463371598132431963368527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3902324261686485235649405 1463371598132431963368527)
                      ·
                        rfl

theorem cell23_2849906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 3, 2, 3, 1, 3].length) (baseStart_2849906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2849906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2849906 prefixEnd_2849906 := by exact prefixLift 2849906
  have htrace : WordTrace (prefixWord ++ tailWord_2849906) baseStart_2849906 baseEnd_2849906 := by
    simpa [prefixWord, tailWord_2849906, baseEnd_2849906] using wordTrace_append hprefix tailTrace_2849906
  have hstable : (prefixWord ++ tailWord_2849906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2849906).length < 2 ^ (prefixWord ++ tailWord_2849906).sum := by decide
  have hdescent : baseEnd_2849906 < baseStart_2849906 := by decide
  rcases family_descends (prefixWord ++ tailWord_2849906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2849923 : List Nat := [1, 1, 1, 3, 3, 2, 4, 3, 1, 1, 3]
def baseStart_2849923 : Nat := 118140960795 + 2849923 * 2 ^ 59
def prefixEnd_2849923 : Nat := 4983230072969 + 3 ^ 40 * 2849923 * 2
def baseEnd_2849923 : Nat := 1463380327303558396855949

theorem tailTrace_2849923 : CollatzResearch.WordTrace tailWord_2849923 prefixEnd_2849923 1463380327303558396855949 := by
  unfold tailWord_2849923
  simp only [CollatzResearch.WordTrace]
  refine ⟨103945231254223173943106423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69296820836148782628737615 103945231254223173943106423)
  ·
    refine ⟨155917846881334760914659635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103945231254223173943106423 155917846881334760914659635)
    ·
      refine ⟨233876770322002141371989453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155917846881334760914659635 233876770322002141371989453)
      ·
        refine ⟨87703788870750803014496045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 233876770322002141371989453 87703788870750803014496045)
        ·
          refine ⟨32888920826531551130436017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 87703788870750803014496045 32888920826531551130436017)
          ·
            refine ⟨24666690619898663347827013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32888920826531551130436017 24666690619898663347827013)
            ·
              refine ⟨4625004491230999377717565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24666690619898663347827013 4625004491230999377717565)
              ·
                refine ⟨1734376684211624766644087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4625004491230999377717565 1734376684211624766644087)
                ·
                  refine ⟨2601565026317437149966131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1734376684211624766644087 2601565026317437149966131)
                  ·
                    refine ⟨3902347539476155724949197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2601565026317437149966131 3902347539476155724949197)
                    ·
                      refine ⟨1463380327303558396855949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3902347539476155724949197 1463380327303558396855949)
                      ·
                        rfl

theorem cell23_2849923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 4, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 4, 3, 1, 1, 3].length) (baseStart_2849923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2849923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2849923 prefixEnd_2849923 := by exact prefixLift 2849923
  have htrace : WordTrace (prefixWord ++ tailWord_2849923) baseStart_2849923 baseEnd_2849923 := by
    simpa [prefixWord, tailWord_2849923, baseEnd_2849923] using wordTrace_append hprefix tailTrace_2849923
  have hstable : (prefixWord ++ tailWord_2849923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2849923).length < 2 ^ (prefixWord ++ tailWord_2849923).sum := by decide
  have hdescent : baseEnd_2849923 < baseStart_2849923 := by decide
  rcases family_descends (prefixWord ++ tailWord_2849923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2849932 : List Nat := [2, 2, 1, 2, 1, 1, 1, 2, 5, 1, 5]
def baseStart_2849932 : Nat := 118140960795 + 2849932 * 2 ^ 59
def prefixEnd_2849932 : Nat := 4983230072969 + 3 ^ 40 * 2849932 * 2
def baseEnd_2849932 : Nat := 1463384948629448861643407

theorem tailTrace_2849932 : CollatzResearch.WordTrace tailWord_2849932 prefixEnd_2849932 1463384948629448861643407 := by
  unfold tailWord_2849932
  simp only [CollatzResearch.WordTrace]
  refine ⟨51972779755595284240092025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69297039674127045653456033 51972779755595284240092025)
  ·
    refine ⟨38979584816696463180069019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51972779755595284240092025 38979584816696463180069019)
    ·
      refine ⟨58469377225044694770103529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38979584816696463180069019 58469377225044694770103529)
      ·
        refine ⟨43852032918783521077577647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58469377225044694770103529 43852032918783521077577647)
        ·
          refine ⟨65778049378175281616366471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43852032918783521077577647 65778049378175281616366471)
          ·
            refine ⟨98667074067262922424549707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65778049378175281616366471 98667074067262922424549707)
            ·
              refine ⟨148000611100894383636824561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 98667074067262922424549707 148000611100894383636824561)
              ·
                refine ⟨111000458325670787727618421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 148000611100894383636824561 111000458325670787727618421)
                ·
                  refine ⟨10406292968031636349464227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 111000458325670787727618421 10406292968031636349464227)
                  ·
                    refine ⟨15609439452047454524196341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10406292968031636349464227 15609439452047454524196341)
                    ·
                      refine ⟨1463384948629448861643407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15609439452047454524196341 1463384948629448861643407)
                      ·
                        rfl

theorem cell23_2849932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 5, 1, 5].length) (baseStart_2849932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2849932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2849932 prefixEnd_2849932 := by exact prefixLift 2849932
  have htrace : WordTrace (prefixWord ++ tailWord_2849932) baseStart_2849932 baseEnd_2849932 := by
    simpa [prefixWord, tailWord_2849932, baseEnd_2849932] using wordTrace_append hprefix tailTrace_2849932
  have hstable : (prefixWord ++ tailWord_2849932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2849932).length < 2 ^ (prefixWord ++ tailWord_2849932).sum := by decide
  have hdescent : baseEnd_2849932 < baseStart_2849932 := by decide
  rcases family_descends (prefixWord ++ tailWord_2849932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2849949 : List Nat := [1, 4, 2, 1, 1, 2, 3, 2, 1, 1, 5]
def baseStart_2849949 : Nat := 118140960795 + 2849949 * 2 ^ 59
def prefixEnd_2849949 : Nat := 4983230072969 + 3 ^ 40 * 2849949 * 2
def baseEnd_2849949 : Nat := 1463393677800575295130829

theorem tailTrace_2849949 : CollatzResearch.WordTrace tailWord_2849949 prefixEnd_2849949 1463393677800575295130829 := by
  unfold tailWord_2849949
  simp only [CollatzResearch.WordTrace]
  refine ⟨103946179552128980383552901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69297453034752653589035267 103946179552128980383552901)
  ·
    refine ⟨19489908666024183821916169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 103946179552128980383552901 19489908666024183821916169)
    ·
      refine ⟨14617431499518137866437127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19489908666024183821916169 14617431499518137866437127)
      ·
        refine ⟨21926147249277206799655691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14617431499518137866437127 21926147249277206799655691)
        ·
          refine ⟨32889220873915810199483537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21926147249277206799655691 32889220873915810199483537)
          ·
            refine ⟨24666915655436857649612653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32889220873915810199483537 24666915655436857649612653)
            ·
              refine ⟨9250093370788821618604745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24666915655436857649612653 9250093370788821618604745)
              ·
                refine ⟨6937570028091616213953559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9250093370788821618604745 6937570028091616213953559)
                ·
                  refine ⟨10406355042137424320930339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6937570028091616213953559 10406355042137424320930339)
                  ·
                    refine ⟨15609532563206136481395509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10406355042137424320930339 15609532563206136481395509)
                    ·
                      refine ⟨1463393677800575295130829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15609532563206136481395509 1463393677800575295130829)
                      ·
                        rfl

theorem cell23_2849949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 3, 2, 1, 1, 5].length) (baseStart_2849949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2849949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2849949 prefixEnd_2849949 := by exact prefixLift 2849949
  have htrace : WordTrace (prefixWord ++ tailWord_2849949) baseStart_2849949 baseEnd_2849949 := by
    simpa [prefixWord, tailWord_2849949, baseEnd_2849949] using wordTrace_append hprefix tailTrace_2849949
  have hstable : (prefixWord ++ tailWord_2849949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2849949).length < 2 ^ (prefixWord ++ tailWord_2849949).sum := by decide
  have hdescent : baseEnd_2849949 < baseStart_2849949 := by decide
  rcases family_descends (prefixWord ++ tailWord_2849949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2849952 : List Nat := [2, 1, 1, 4, 2, 1, 2, 10]
def baseStart_2849952 : Nat := 118140960795 + 2849952 * 2 ^ 59
def prefixEnd_2849952 : Nat := 4983230072969 + 3 ^ 40 * 2849952 * 2
def baseEnd_2849952 : Nat := 54199822897871806792345

theorem tailTrace_2849952 : CollatzResearch.WordTrace tailWord_2849952 prefixEnd_2849952 54199822897871806792345 := by
  unfold tailWord_2849952
  simp only [CollatzResearch.WordTrace]
  refine ⟨51973144485559055947956055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69297525980745407930608073 51973144485559055947956055)
  ·
    refine ⟨77959716728338583921934083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51973144485559055947956055 77959716728338583921934083)
    ·
      refine ⟨116939575092507875882901125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77959716728338583921934083 116939575092507875882901125)
      ·
        refine ⟨21926170329845226728043961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 116939575092507875882901125 21926170329845226728043961)
        ·
          refine ⟨16444627747383920046032971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21926170329845226728043961 16444627747383920046032971)
          ·
            refine ⟨24666941621075880069049457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16444627747383920046032971 24666941621075880069049457)
            ·
              refine ⟨18500206215806910051787093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24666941621075880069049457 18500206215806910051787093)
              ·
                refine ⟨54199822897871806792345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 18500206215806910051787093 54199822897871806792345)
                ·
                  rfl

theorem cell23_2849952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 2, 10].length) (baseStart_2849952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2849952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2849952 prefixEnd_2849952 := by exact prefixLift 2849952
  have htrace : WordTrace (prefixWord ++ tailWord_2849952) baseStart_2849952 baseEnd_2849952 := by
    simpa [prefixWord, tailWord_2849952, baseEnd_2849952] using wordTrace_append hprefix tailTrace_2849952
  have hstable : (prefixWord ++ tailWord_2849952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2849952).length < 2 ^ (prefixWord ++ tailWord_2849952).sum := by decide
  have hdescent : baseEnd_2849952 < baseStart_2849952 := by decide
  rcases family_descends (prefixWord ++ tailWord_2849952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2849956 : List Nat := [2, 3, 1, 2, 3, 3, 1, 1, 1, 6]
def baseStart_2849956 : Nat := 118140960795 + 2849956 * 2 ^ 59
def prefixEnd_2849956 : Nat := 4983230072969 + 3 ^ 40 * 2849956 * 2
def baseEnd_2849956 : Nat := 487799090721718922581099

theorem tailTrace_2849956 : CollatzResearch.WordTrace tailWord_2849956 prefixEnd_2849956 487799090721718922581099 := by
  unfold tailWord_2849956
  simp only [CollatzResearch.WordTrace]
  refine ⟨51973217431551810289528861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69297623242069080386038481 51973217431551810289528861)
  ·
    refine ⟨19489956536831928858573323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51973217431551810289528861 19489956536831928858573323)
    ·
      refine ⟨29234934805247893287859985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19489956536831928858573323 29234934805247893287859985)
      ·
        refine ⟨21926201103935919965894989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29234934805247893287859985 21926201103935919965894989)
        ·
          refine ⟨8222325413975969987210621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21926201103935919965894989 8222325413975969987210621)
          ·
            refine ⟨3083372030240988745203983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8222325413975969987210621 3083372030240988745203983)
            ·
              refine ⟨4625058045361483117805975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3083372030240988745203983 4625058045361483117805975)
              ·
                refine ⟨6937587068042224676708963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4625058045361483117805975 6937587068042224676708963)
                ·
                  refine ⟨10406380602063337015063445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6937587068042224676708963 10406380602063337015063445)
                  ·
                    refine ⟨487799090721718922581099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10406380602063337015063445 487799090721718922581099)
                    ·
                      rfl

theorem cell23_2849956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 3, 1, 1, 1, 6].length) (baseStart_2849956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2849956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2849956 prefixEnd_2849956 := by exact prefixLift 2849956
  have htrace : WordTrace (prefixWord ++ tailWord_2849956) baseStart_2849956 baseEnd_2849956 := by
    simpa [prefixWord, tailWord_2849956, baseEnd_2849956] using wordTrace_append hprefix tailTrace_2849956
  have hstable : (prefixWord ++ tailWord_2849956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2849956).length < 2 ^ (prefixWord ++ tailWord_2849956).sum := by decide
  have hdescent : baseEnd_2849956 < baseStart_2849956 := by decide
  rcases family_descends (prefixWord ++ tailWord_2849956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2849969 : List Nat := [1, 2, 2, 5, 1, 2, 1, 9]
def baseStart_2849969 : Nat := 118140960795 + 2849969 * 2 ^ 59
def prefixEnd_2849969 : Nat := 4983230072969 + 3 ^ 40 * 2849969 * 2
def baseEnd_2849969 : Nat := 54200146200506119143731

theorem tailTrace_2849969 : CollatzResearch.WordTrace tailWord_2849969 prefixEnd_2849969 54200146200506119143731 := by
  unfold tailWord_2849969
  simp only [CollatzResearch.WordTrace]
  refine ⟨103946909012056523799280961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69297939341371015866187307 103946909012056523799280961)
  ·
    refine ⟨77960181759042392849460721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103946909012056523799280961 77960181759042392849460721)
    ·
      refine ⟨58470136319281794637095541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77960181759042392849460721 58470136319281794637095541)
      ·
        refine ⟨5481575279932668247227707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 58470136319281794637095541 5481575279932668247227707)
        ·
          refine ⟨8222362919899002370841561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5481575279932668247227707 8222362919899002370841561)
          ·
            refine ⟨6166772189924251778131171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8222362919899002370841561 6166772189924251778131171)
            ·
              refine ⟨9250158284886377667196757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6166772189924251778131171 9250158284886377667196757)
              ·
                refine ⟨54200146200506119143731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 9250158284886377667196757 54200146200506119143731)
                ·
                  rfl

theorem cell23_2849969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 1, 9].length) (baseStart_2849969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2849969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2849969 prefixEnd_2849969 := by exact prefixLift 2849969
  have htrace : WordTrace (prefixWord ++ tailWord_2849969) baseStart_2849969 baseEnd_2849969 := by
    simpa [prefixWord, tailWord_2849969, baseEnd_2849969] using wordTrace_append hprefix tailTrace_2849969
  have hstable : (prefixWord ++ tailWord_2849969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2849969).length < 2 ^ (prefixWord ++ tailWord_2849969).sum := by decide
  have hdescent : baseEnd_2849969 < baseStart_2849969 := by decide
  rcases family_descends (prefixWord ++ tailWord_2849969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2850136 : List Nat := [2, 1, 2, 2, 1, 1, 3, 4, 3, 4]
def baseStart_2850136 : Nat := 118140960795 + 2850136 * 2 ^ 59
def prefixEnd_2850136 : Nat := 4983230072969 + 3 ^ 40 * 2850136 * 2
def baseEnd_2850136 : Nat := 487829899560988687830823

theorem tailTrace_2850136 : CollatzResearch.WordTrace tailWord_2850136 prefixEnd_2850136 487829899560988687830823 := by
  unfold tailWord_2850136
  simp only [CollatzResearch.WordTrace]
  refine ⟨51976500001225755660305131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69302000001634340880406841 51976500001225755660305131)
  ·
    refine ⟨77964750001838633490457697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51976500001225755660305131 77964750001838633490457697)
    ·
      refine ⟨58473562501378975117843273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77964750001838633490457697 58473562501378975117843273)
      ·
        refine ⟨43855171876034231338382455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58473562501378975117843273 43855171876034231338382455)
        ·
          refine ⟨65782757814051347007573683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43855171876034231338382455 65782757814051347007573683)
          ·
            refine ⟨98674136721077020511360525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65782757814051347007573683 98674136721077020511360525)
            ·
              refine ⟨37002801270403882691760197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 98674136721077020511360525 37002801270403882691760197)
              ·
                refine ⟨6938025238200728004705037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37002801270403882691760197 6938025238200728004705037)
                ·
                  refine ⟨2601759464325273001764389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6938025238200728004705037 2601759464325273001764389)
                  ·
                    refine ⟨487829899560988687830823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2601759464325273001764389 487829899560988687830823)
                    ·
                      rfl

theorem cell23_2850136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 4, 3, 4].length) (baseStart_2850136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2850136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2850136 prefixEnd_2850136 := by exact prefixLift 2850136
  have htrace : WordTrace (prefixWord ++ tailWord_2850136) baseStart_2850136 baseEnd_2850136 := by
    simpa [prefixWord, tailWord_2850136, baseEnd_2850136] using wordTrace_append hprefix tailTrace_2850136
  have hstable : (prefixWord ++ tailWord_2850136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2850136).length < 2 ^ (prefixWord ++ tailWord_2850136).sum := by decide
  have hdescent : baseEnd_2850136 < baseStart_2850136 := by decide
  rcases family_descends (prefixWord ++ tailWord_2850136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2850149 : List Nat := [1, 3, 1, 3, 1, 2, 1, 1, 10]
def baseStart_2850149 : Nat := 118140960795 + 2850149 * 2 ^ 59
def prefixEnd_2850149 : Nat := 4983230072969 + 3 ^ 40 * 2850149 * 2
def baseEnd_2850149 : Nat := 162610708214608279181101

theorem tailTrace_2850149 : CollatzResearch.WordTrace tailWord_2850149 prefixEnd_2850149 162610708214608279181101 := by
  unfold tailWord_2850149
  simp only [CollatzResearch.WordTrace]
  refine ⟨103953474151404414540833501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69302316100936276360555667 103953474151404414540833501)
  ·
    refine ⟨38982552806776655452812563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 103953474151404414540833501 38982552806776655452812563)
    ·
      refine ⟨58473829210164983179218845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38982552806776655452812563 58473829210164983179218845)
      ·
        refine ⟨21927685953811868692207067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58473829210164983179218845 21927685953811868692207067)
        ·
          refine ⟨32891528930717803038310601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21927685953811868692207067 32891528930717803038310601)
          ·
            refine ⟨24668646698038352278732951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32891528930717803038310601 24668646698038352278732951)
            ·
              refine ⟨37002970047057528418099427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24668646698038352278732951 37002970047057528418099427)
              ·
                refine ⟨55504455070586292627149141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37002970047057528418099427 55504455070586292627149141)
                ·
                  refine ⟨162610708214608279181101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 55504455070586292627149141 162610708214608279181101)
                  ·
                    rfl

theorem cell23_2850149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 1, 10].length) (baseStart_2850149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2850149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2850149 prefixEnd_2850149 := by exact prefixLift 2850149
  have htrace : WordTrace (prefixWord ++ tailWord_2850149) baseStart_2850149 baseEnd_2850149 := by
    simpa [prefixWord, tailWord_2850149, baseEnd_2850149] using wordTrace_append hprefix tailTrace_2850149
  have hstable : (prefixWord ++ tailWord_2850149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2850149).length < 2 ^ (prefixWord ++ tailWord_2850149).sum := by decide
  have hdescent : baseEnd_2850149 < baseStart_2850149 := by decide
  rcases family_descends (prefixWord ++ tailWord_2850149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2850153 : List Nat := [1, 2, 1, 1, 1, 3, 2, 7, 1, 4]
def baseStart_2850153 : Nat := 118140960795 + 2850153 * 2 ^ 59
def prefixEnd_2850153 : Nat := 4983230072969 + 3 ^ 40 * 2850153 * 2
def baseEnd_2850153 : Nat := 487832809284697498993297

theorem tailTrace_2850153 : CollatzResearch.WordTrace tailWord_2850153 prefixEnd_2850153 487832809284697498993297 := by
  unfold tailWord_2850153
  simp only [CollatzResearch.WordTrace]
  refine ⟨103953620043389923223979113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69302413362259948815986075 103953620043389923223979113)
  ·
    refine ⟨77965215032542442417984335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103953620043389923223979113 77965215032542442417984335)
    ·
      refine ⟨116947822548813663626976503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77965215032542442417984335 116947822548813663626976503)
      ·
        refine ⟨175421733823220495440464755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116947822548813663626976503 175421733823220495440464755)
        ·
          refine ⟨263132600734830743160697133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 175421733823220495440464755 263132600734830743160697133)
          ·
            refine ⟨98674725275561528685261425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 263132600734830743160697133 98674725275561528685261425)
            ·
              refine ⟨74006043956671146513946069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 98674725275561528685261425 74006043956671146513946069)
              ·
                refine ⟨1734516655234479996420611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 74006043956671146513946069 1734516655234479996420611)
                ·
                  refine ⟨2601774982851719994630917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1734516655234479996420611 2601774982851719994630917)
                  ·
                    refine ⟨487832809284697498993297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2601774982851719994630917 487832809284697498993297)
                    ·
                      rfl

theorem cell23_2850153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 7, 1, 4].length) (baseStart_2850153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2850153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2850153 prefixEnd_2850153 := by exact prefixLift 2850153
  have htrace : WordTrace (prefixWord ++ tailWord_2850153) baseStart_2850153 baseEnd_2850153 := by
    simpa [prefixWord, tailWord_2850153, baseEnd_2850153] using wordTrace_append hprefix tailTrace_2850153
  have hstable : (prefixWord ++ tailWord_2850153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2850153).length < 2 ^ (prefixWord ++ tailWord_2850153).sum := by decide
  have hdescent : baseEnd_2850153 < baseStart_2850153 := by decide
  rcases family_descends (prefixWord ++ tailWord_2850153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2850169 : List Nat := [1, 2, 1, 3, 2, 1, 2, 1, 1, 1, 8]
def baseStart_2850169 : Nat := 118140960795 + 2850169 * 2 ^ 59
def prefixEnd_2850169 : Nat := 4983230072969 + 3 ^ 40 * 2850169 * 2
def baseEnd_2850169 : Nat := 1463506643544564434379817

theorem tailTrace_2850169 : CollatzResearch.WordTrace tailWord_2850169 prefixEnd_2850169 1463506643544564434379817 := by
  unfold tailWord_2850169
  simp only [CollatzResearch.WordTrace]
  refine ⟨103954203611331957956561561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69302802407554638637707707 103954203611331957956561561)
  ·
    refine ⟨77965652708498968467421171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103954203611331957956561561 77965652708498968467421171)
    ·
      refine ⟨116948479062748452701131757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77965652708498968467421171 116948479062748452701131757)
      ·
        refine ⟨43855679648530669762924409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 116948479062748452701131757 43855679648530669762924409)
        ·
          refine ⟨32891759736398002322193307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43855679648530669762924409 32891759736398002322193307)
          ·
            refine ⟨49337639604597003483289961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32891759736398002322193307 49337639604597003483289961)
            ·
              refine ⟨37003229703447752612467471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49337639604597003483289961 37003229703447752612467471)
              ·
                refine ⟨55504844555171628918701207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37003229703447752612467471 55504844555171628918701207)
                ·
                  refine ⟨83257266832757443378051811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 55504844555171628918701207 83257266832757443378051811)
                  ·
                    refine ⟨124885900249136165067077717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 83257266832757443378051811 124885900249136165067077717)
                    ·
                      refine ⟨1463506643544564434379817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 124885900249136165067077717 1463506643544564434379817)
                      ·
                        rfl

theorem cell23_2850169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 1, 1, 1, 8].length) (baseStart_2850169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2850169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2850169 prefixEnd_2850169 := by exact prefixLift 2850169
  have htrace : WordTrace (prefixWord ++ tailWord_2850169) baseStart_2850169 baseEnd_2850169 := by
    simpa [prefixWord, tailWord_2850169, baseEnd_2850169] using wordTrace_append hprefix tailTrace_2850169
  have hstable : (prefixWord ++ tailWord_2850169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2850169).length < 2 ^ (prefixWord ++ tailWord_2850169).sum := by decide
  have hdescent : baseEnd_2850169 < baseStart_2850169 := by decide
  rcases family_descends (prefixWord ++ tailWord_2850169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2850183 : List Nat := [1, 1, 4, 2, 2, 2, 4, 1, 6]
def baseStart_2850183 : Nat := 118140960795 + 2850183 * 2 ^ 59
def prefixEnd_2850183 : Nat := 4983230072969 + 3 ^ 40 * 2850183 * 2
def baseEnd_2850183 : Nat := 162612648030414153289417

theorem tailTrace_2850183 : CollatzResearch.WordTrace tailWord_2850183 prefixEnd_2850183 162612648030414153289417 := by
  unfold tailWord_2850183
  simp only [CollatzResearch.WordTrace]
  refine ⟨103954714233281238347571203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69303142822187492231714135 103954714233281238347571203)
  ·
    refine ⟨155932071349921857521356805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103954714233281238347571203 155932071349921857521356805)
    ·
      refine ⟨29237263378110348285254401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 155932071349921857521356805 29237263378110348285254401)
      ·
        refine ⟨21927947533582761213940801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29237263378110348285254401 21927947533582761213940801)
        ·
          refine ⟨16445960650187070910455601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21927947533582761213940801 16445960650187070910455601)
          ·
            refine ⟨12334470487640303182841701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16445960650187070910455601 12334470487640303182841701)
            ·
              refine ⟨2312713216432556846782819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12334470487640303182841701 2312713216432556846782819)
              ·
                refine ⟨3469069824648835270174229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2312713216432556846782819 3469069824648835270174229)
                ·
                  refine ⟨162612648030414153289417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3469069824648835270174229 162612648030414153289417)
                  ·
                    rfl

theorem cell23_2850183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 4, 1, 6].length) (baseStart_2850183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2850183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2850183 prefixEnd_2850183 := by exact prefixLift 2850183
  have htrace : WordTrace (prefixWord ++ tailWord_2850183) baseStart_2850183 baseEnd_2850183 := by
    simpa [prefixWord, tailWord_2850183, baseEnd_2850183] using wordTrace_append hprefix tailTrace_2850183
  have hstable : (prefixWord ++ tailWord_2850183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2850183).length < 2 ^ (prefixWord ++ tailWord_2850183).sum := by decide
  have hdescent : baseEnd_2850183 < baseStart_2850183 := by decide
  rcases family_descends (prefixWord ++ tailWord_2850183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2850243 : List Nat := [1, 1, 1, 3, 1, 1, 6, 3, 2, 4]
def baseStart_2850243 : Nat := 118140960795 + 2850243 * 2 ^ 59
def prefixEnd_2850243 : Nat := 4983230072969 + 3 ^ 40 * 2850243 * 2
def baseEnd_2850243 : Nat := 487848213704332381618159

theorem tailTrace_2850243 : CollatzResearch.WordTrace tailWord_2850243 prefixEnd_2850243 487848213704332381618159 := by
  unfold tailWord_2850243
  simp only [CollatzResearch.WordTrace]
  refine ⟨103956902613063868594755383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69304601742042579063170255 103956902613063868594755383)
  ·
    refine ⟨155935353919595802892133075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103956902613063868594755383 155935353919595802892133075)
    ·
      refine ⟨233903030879393704338199613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155935353919595802892133075 233903030879393704338199613)
      ·
        refine ⟨87713636579772639126824855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 233903030879393704338199613 87713636579772639126824855)
        ·
          refine ⟨131570454869658958690237283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87713636579772639126824855 131570454869658958690237283)
          ·
            refine ⟨197355682304488438035355925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 131570454869658958690237283 197355682304488438035355925)
            ·
              refine ⟨9251047608022895532907309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 197355682304488438035355925 9251047608022895532907309)
              ·
                refine ⟨3469142853008585824840241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9251047608022895532907309 3469142853008585824840241)
                ·
                  refine ⟨2601857139756439368630181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3469142853008585824840241 2601857139756439368630181)
                  ·
                    refine ⟨487848213704332381618159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2601857139756439368630181 487848213704332381618159)
                    ·
                      rfl

theorem cell23_2850243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 6, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 6, 3, 2, 4].length) (baseStart_2850243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2850243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2850243 prefixEnd_2850243 := by exact prefixLift 2850243
  have htrace : WordTrace (prefixWord ++ tailWord_2850243) baseStart_2850243 baseEnd_2850243 := by
    simpa [prefixWord, tailWord_2850243, baseEnd_2850243] using wordTrace_append hprefix tailTrace_2850243
  have hstable : (prefixWord ++ tailWord_2850243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2850243).length < 2 ^ (prefixWord ++ tailWord_2850243).sum := by decide
  have hdescent : baseEnd_2850243 < baseStart_2850243 := by decide
  rcases family_descends (prefixWord ++ tailWord_2850243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2850250 : List Nat := [3, 1, 2, 1, 2, 3, 1, 1, 5, 2, 2]
def baseStart_2850250 : Nat := 118140960795 + 2850250 * 2 ^ 59
def prefixEnd_2850250 : Nat := 4983230072969 + 3 ^ 40 * 2850250 * 2
def baseEnd_2850250 : Nat := 1463548235477578617466945

theorem tailTrace_2850250 : CollatzResearch.WordTrace tailWord_2850250 prefixEnd_2850250 1463548235477578617466945 := by
  unfold tailWord_2850250
  simp only [CollatzResearch.WordTrace]
  refine ⟨25989289481009627197565051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69304771949359005860173469 25989289481009627197565051)
  ·
    refine ⟨38983934221514440796347577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25989289481009627197565051 38983934221514440796347577)
    ·
      refine ⟨29237950666135830597260683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38983934221514440796347577 29237950666135830597260683)
      ·
        refine ⟨43856925999203745895891025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29237950666135830597260683 43856925999203745895891025)
        ·
          refine ⟨32892694499402809421918269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43856925999203745895891025 32892694499402809421918269)
          ·
            refine ⟨12334760437276053533219351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32892694499402809421918269 12334760437276053533219351)
            ·
              refine ⟨18502140655914080299829027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12334760437276053533219351 18502140655914080299829027)
              ·
                refine ⟨27753210983871120449743541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18502140655914080299829027 27753210983871120449743541)
                ·
                  refine ⟨2601863529737917542163457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 27753210983871120449743541 2601863529737917542163457)
                  ·
                    refine ⟨1951397647303438156622593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2601863529737917542163457 1951397647303438156622593)
                    ·
                      refine ⟨1463548235477578617466945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1951397647303438156622593 1463548235477578617466945)
                      ·
                        rfl

theorem cell23_2850250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 1, 1, 5, 2, 2].length) (baseStart_2850250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2850250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2850250 prefixEnd_2850250 := by exact prefixLift 2850250
  have htrace : WordTrace (prefixWord ++ tailWord_2850250) baseStart_2850250 baseEnd_2850250 := by
    simpa [prefixWord, tailWord_2850250, baseEnd_2850250] using wordTrace_append hprefix tailTrace_2850250
  have hstable : (prefixWord ++ tailWord_2850250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2850250).length < 2 ^ (prefixWord ++ tailWord_2850250).sum := by decide
  have hdescent : baseEnd_2850250 < baseStart_2850250 := by decide
  rcases family_descends (prefixWord ++ tailWord_2850250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2850277 : List Nat := [1, 3, 1, 5, 1, 3, 1, 2, 2, 4]
def baseStart_2850277 : Nat := 118140960795 + 2850277 * 2 ^ 59
def prefixEnd_2850277 : Nat := 4983230072969 + 3 ^ 40 * 2850277 * 2
def baseEnd_2850277 : Nat := 487854033151750003943107

theorem tailTrace_2850277 : CollatzResearch.WordTrace tailWord_2850277 prefixEnd_2850277 487854033151750003943107 := by
  unfold tailWord_2850277
  simp only [CollatzResearch.WordTrace]
  refine ⟨103958142694940692401493085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69305428463293794934328723 103958142694940692401493085)
  ·
    refine ⟨38984303510602759650559907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 103958142694940692401493085 38984303510602759650559907)
    ·
      refine ⟨58476455265904139475839861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38984303510602759650559907 58476455265904139475839861)
      ·
        refine ⟨5482167681178513075859987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 58476455265904139475839861 5482167681178513075859987)
        ·
          refine ⟨8223251521767769613789981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5482167681178513075859987 8223251521767769613789981)
          ·
            refine ⟨3083719320662913605171243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8223251521767769613789981 3083719320662913605171243)
            ·
              refine ⟨4625578980994370407756865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3083719320662913605171243 4625578980994370407756865)
              ·
                refine ⟨3469184235745777805817649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4625578980994370407756865 3469184235745777805817649)
                ·
                  refine ⟨2601888176809333354363237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3469184235745777805817649 2601888176809333354363237)
                  ·
                    refine ⟨487854033151750003943107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2601888176809333354363237 487854033151750003943107)
                    ·
                      rfl

theorem cell23_2850277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 3, 1, 2, 2, 4].length) (baseStart_2850277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2850277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2850277 prefixEnd_2850277 := by exact prefixLift 2850277
  have htrace : WordTrace (prefixWord ++ tailWord_2850277) baseStart_2850277 baseEnd_2850277 := by
    simpa [prefixWord, tailWord_2850277, baseEnd_2850277] using wordTrace_append hprefix tailTrace_2850277
  have hstable : (prefixWord ++ tailWord_2850277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2850277).length < 2 ^ (prefixWord ++ tailWord_2850277).sum := by decide
  have hdescent : baseEnd_2850277 < baseStart_2850277 := by decide
  rcases family_descends (prefixWord ++ tailWord_2850277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2850300 : List Nat := [2, 2, 2, 1, 2, 1, 2, 5, 2, 1, 3]
def baseStart_2850300 : Nat := 118140960795 + 2850300 * 2 ^ 59
def prefixEnd_2850300 : Nat := 4983230072969 + 3 ^ 40 * 2850300 * 2
def baseEnd_2850300 : Nat := 1463573909510303421841715

theorem tailTrace_2850300 : CollatzResearch.WordTrace tailWord_2850300 prefixEnd_2850300 1463573909510303421841715 := by
  unfold tailWord_2850300
  simp only [CollatzResearch.WordTrace]
  refine ⟨51979490786928683664790177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69305987715904911553053569 51979490786928683664790177)
  ·
    refine ⟨38984618090196512748592633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51979490786928683664790177 38984618090196512748592633)
    ·
      refine ⟨29238463567647384561444475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38984618090196512748592633 29238463567647384561444475)
      ·
        refine ⟨43857695351471076842166713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29238463567647384561444475 43857695351471076842166713)
        ·
          refine ⟨32893271513603307631625035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43857695351471076842166713 32893271513603307631625035)
          ·
            refine ⟨49339907270404961447437553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32893271513603307631625035 49339907270404961447437553)
            ·
              refine ⟨37004930452803721085578165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49339907270404961447437553 37004930452803721085578165)
              ·
                refine ⟨3469212229950348851772953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 37004930452803721085578165 3469212229950348851772953)
                ·
                  refine ⟨2601909172462761638829715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3469212229950348851772953 2601909172462761638829715)
                  ·
                    refine ⟨3902863758694142458244573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2601909172462761638829715 3902863758694142458244573)
                    ·
                      refine ⟨1463573909510303421841715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3902863758694142458244573 1463573909510303421841715)
                      ·
                        rfl

theorem cell23_2850300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 5, 2, 1, 3].length) (baseStart_2850300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2850300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2850300 prefixEnd_2850300 := by exact prefixLift 2850300
  have htrace : WordTrace (prefixWord ++ tailWord_2850300) baseStart_2850300 baseEnd_2850300 := by
    simpa [prefixWord, tailWord_2850300, baseEnd_2850300] using wordTrace_append hprefix tailTrace_2850300
  have hstable : (prefixWord ++ tailWord_2850300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2850300).length < 2 ^ (prefixWord ++ tailWord_2850300).sum := by decide
  have hdescent : baseEnd_2850300 < baseStart_2850300 := by decide
  rcases family_descends (prefixWord ++ tailWord_2850300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2850318 : List Nat := [4, 1, 1, 2, 5, 1, 1, 3, 1, 2, 2]
def baseStart_2850318 : Nat := 118140960795 + 2850318 * 2 ^ 59
def prefixEnd_2850318 : Nat := 4983230072969 + 3 ^ 40 * 2850318 * 2
def baseEnd_2850318 : Nat := 1463583152162084351416633

theorem tailTrace_2850318 : CollatzResearch.WordTrace tailWord_2850318 prefixEnd_2850318 1463583152162084351416633 := by
  unfold tailWord_2850318
  simp only [CollatzResearch.WordTrace]
  refine ⟨12994954760974019550466951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 69306425391861437602490405 12994954760974019550466951)
  ·
    refine ⟨19492432141461029325700427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12994954760974019550466951 19492432141461029325700427)
    ·
      refine ⟨29238648212191543988550641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19492432141461029325700427 29238648212191543988550641)
      ·
        refine ⟨21928986159143657991412981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29238648212191543988550641 21928986159143657991412981)
        ·
          refine ⟨2055842452419717936694967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 21928986159143657991412981 2055842452419717936694967)
          ·
            refine ⟨3083763678629576905042451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2055842452419717936694967 3083763678629576905042451)
            ·
              refine ⟨4625645517944365357563677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3083763678629576905042451 4625645517944365357563677)
              ·
                refine ⟨1734617069229137009086379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4625645517944365357563677 1734617069229137009086379)
                ·
                  refine ⟨2601925603843705513629569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1734617069229137009086379 2601925603843705513629569)
                  ·
                    refine ⟨1951444202882779135222177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2601925603843705513629569 1951444202882779135222177)
                    ·
                      refine ⟨1463583152162084351416633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1951444202882779135222177 1463583152162084351416633)
                      ·
                        rfl

theorem cell23_2850318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 5, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 5, 1, 1, 3, 1, 2, 2].length) (baseStart_2850318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2850318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2850318 prefixEnd_2850318 := by exact prefixLift 2850318
  have htrace : WordTrace (prefixWord ++ tailWord_2850318) baseStart_2850318 baseEnd_2850318 := by
    simpa [prefixWord, tailWord_2850318, baseEnd_2850318] using wordTrace_append hprefix tailTrace_2850318
  have hstable : (prefixWord ++ tailWord_2850318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2850318).length < 2 ^ (prefixWord ++ tailWord_2850318).sum := by decide
  have hdescent : baseEnd_2850318 < baseStart_2850318 := by decide
  rcases family_descends (prefixWord ++ tailWord_2850318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2850403 : List Nat := [1, 1, 1, 5, 1, 3, 2, 1, 1, 2, 5]
def baseStart_2850403 : Nat := 118140960795 + 2850403 * 2 ^ 59
def prefixEnd_2850403 : Nat := 4983230072969 + 3 ^ 40 * 2850403 * 2
def baseEnd_2850403 : Nat := 1463626798017716518853741

theorem tailTrace_2850403 : CollatzResearch.WordTrace tailWord_2850403 prefixEnd_2850403 1463626798017716518853741 := by
  unfold tailWord_2850403
  simp only [CollatzResearch.WordTrace]
  refine ⟨103962738292484215920579863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69308492194989477280386575 103962738292484215920579863)
  ·
    refine ⟨155944107438726323880869795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103962738292484215920579863 155944107438726323880869795)
    ·
      refine ⟨233916161158089485821304693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155944107438726323880869795 233916161158089485821304693)
      ·
        refine ⟨21929640108570889295747315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 233916161158089485821304693 21929640108570889295747315)
        ·
          refine ⟨32894460162856333943620973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21929640108570889295747315 32894460162856333943620973)
          ·
            refine ⟨12335422561071125228857865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32894460162856333943620973 12335422561071125228857865)
            ·
              refine ⟨9251566920803343921643399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12335422561071125228857865 9251566920803343921643399)
              ·
                refine ⟨13877350381205015882465099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9251566920803343921643399 13877350381205015882465099)
                ·
                  refine ⟨20816025571807523823697649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13877350381205015882465099 20816025571807523823697649)
                  ·
                    refine ⟨15612019178855642867773237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20816025571807523823697649 15612019178855642867773237)
                    ·
                      refine ⟨1463626798017716518853741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15612019178855642867773237 1463626798017716518853741)
                      ·
                        rfl

theorem cell23_2850403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 2, 1, 1, 2, 5].length) (baseStart_2850403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2850403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2850403 prefixEnd_2850403 := by exact prefixLift 2850403
  have htrace : WordTrace (prefixWord ++ tailWord_2850403) baseStart_2850403 baseEnd_2850403 := by
    simpa [prefixWord, tailWord_2850403, baseEnd_2850403] using wordTrace_append hprefix tailTrace_2850403
  have hstable : (prefixWord ++ tailWord_2850403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2850403).length < 2 ^ (prefixWord ++ tailWord_2850403).sum := by decide
  have hdescent : baseEnd_2850403 < baseStart_2850403 := by decide
  rcases family_descends (prefixWord ++ tailWord_2850403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2850514 : List Nat := [3, 2, 2, 2, 2, 1, 3, 1, 3, 1, 3]
def baseStart_2850514 : Nat := 118140960795 + 2850514 * 2 ^ 59
def prefixEnd_2850514 : Nat := 4983230072969 + 3 ^ 40 * 2850514 * 2
def baseEnd_2850514 : Nat := 1463683794370365584565731

theorem tailTrace_2850514 : CollatzResearch.WordTrace tailWord_2850514 prefixEnd_2850514 1463683794370365584565731 := by
  unfold tailWord_2850514
  simp only [CollatzResearch.WordTrace]
  refine ⟨25991696698770520469467649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69311191196721387918580397 25991696698770520469467649)
  ·
    refine ⟨19493772524077890352100737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25991696698770520469467649 19493772524077890352100737)
    ·
      refine ⟨14620329393058417764075553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19493772524077890352100737 14620329393058417764075553)
      ·
        refine ⟨10965247044793813323056665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14620329393058417764075553 10965247044793813323056665)
        ·
          refine ⟨8223935283595359992292499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10965247044793813323056665 8223935283595359992292499)
          ·
            refine ⟨12335902925393039988438749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8223935283595359992292499 12335902925393039988438749)
            ·
              refine ⟨4625963597022389995664531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12335902925393039988438749 4625963597022389995664531)
              ·
                refine ⟨6938945395533584993496797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4625963597022389995664531 6938945395533584993496797)
                ·
                  refine ⟨2602104523325094372561299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6938945395533584993496797 2602104523325094372561299)
                  ·
                    refine ⟨3903156784987641558841949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2602104523325094372561299 3903156784987641558841949)
                    ·
                      refine ⟨1463683794370365584565731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3903156784987641558841949 1463683794370365584565731)
                      ·
                        rfl

theorem cell23_2850514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 3, 1, 3, 1, 3].length) (baseStart_2850514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2850514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2850514 prefixEnd_2850514 := by exact prefixLift 2850514
  have htrace : WordTrace (prefixWord ++ tailWord_2850514) baseStart_2850514 baseEnd_2850514 := by
    simpa [prefixWord, tailWord_2850514, baseEnd_2850514] using wordTrace_append hprefix tailTrace_2850514
  have hstable : (prefixWord ++ tailWord_2850514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2850514).length < 2 ^ (prefixWord ++ tailWord_2850514).sum := by decide
  have hdescent : baseEnd_2850514 < baseStart_2850514 := by decide
  rcases family_descends (prefixWord ++ tailWord_2850514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2850520 : List Nat := [2, 1, 2, 2, 3, 1, 2, 2, 3, 1, 4]
def baseStart_2850520 : Nat := 118140960795 + 2850520 * 2 ^ 59
def prefixEnd_2850520 : Nat := 4983230072969 + 3 ^ 40 * 2850520 * 2
def baseEnd_2850520 : Nat := 1463686875254292561090703

theorem tailTrace_2850520 : CollatzResearch.WordTrace tailWord_2850520 prefixEnd_2850520 1463686875254292561090703 := by
  unfold tailWord_2850520
  simp only [CollatzResearch.WordTrace]
  refine ⟨51983502816530172451294507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69311337088706896601726009 51983502816530172451294507)
  ·
    refine ⟨77975254224795258676941761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51983502816530172451294507 77975254224795258676941761)
    ·
      refine ⟨58481440668596444007706321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77975254224795258676941761 58481440668596444007706321)
      ·
        refine ⟨43861080501447333005779741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58481440668596444007706321 43861080501447333005779741)
        ·
          refine ⟨16447905188042749877167403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43861080501447333005779741 16447905188042749877167403)
          ·
            refine ⟨24671857782064124815751105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16447905188042749877167403 24671857782064124815751105)
            ·
              refine ⟨18503893336548093611813329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24671857782064124815751105 18503893336548093611813329)
              ·
                refine ⟨13877920002411070208859997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18503893336548093611813329 13877920002411070208859997)
                ·
                  refine ⟨5204220000904151328322499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13877920002411070208859997 5204220000904151328322499)
                  ·
                    refine ⟨7806330001356226992483749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5204220000904151328322499 7806330001356226992483749)
                    ·
                      refine ⟨1463686875254292561090703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7806330001356226992483749 1463686875254292561090703)
                      ·
                        rfl

theorem cell23_2850520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 2, 2, 3, 1, 4].length) (baseStart_2850520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2850520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2850520 prefixEnd_2850520 := by exact prefixLift 2850520
  have htrace : WordTrace (prefixWord ++ tailWord_2850520) baseStart_2850520 baseEnd_2850520 := by
    simpa [prefixWord, tailWord_2850520, baseEnd_2850520] using wordTrace_append hprefix tailTrace_2850520
  have hstable : (prefixWord ++ tailWord_2850520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2850520).length < 2 ^ (prefixWord ++ tailWord_2850520).sum := by decide
  have hdescent : baseEnd_2850520 < baseStart_2850520 := by decide
  rcases family_descends (prefixWord ++ tailWord_2850520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2850537 : List Nat := [1, 2, 1, 1, 1, 2, 3, 3, 5, 2, 2]
def baseStart_2850537 : Nat := 118140960795 + 2850537 * 2 ^ 59
def prefixEnd_2850537 : Nat := 4983230072969 + 3 ^ 40 * 2850537 * 2
def baseEnd_2850537 : Nat := 1463695604425418994578125

theorem tailTrace_2850537 : CollatzResearch.WordTrace tailWord_2850537 prefixEnd_2850537 1463695604425418994578125 := by
  unfold tailWord_2850537
  simp only [CollatzResearch.WordTrace]
  refine ⟨103967625673998756805957865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69311750449332504537305243 103967625673998756805957865)
  ·
    refine ⟨77975719255499067604468399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103967625673998756805957865 77975719255499067604468399)
    ·
      refine ⟨116963578883248601406702599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77975719255499067604468399 116963578883248601406702599)
      ·
        refine ⟨175445368324872902110053899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116963578883248601406702599 175445368324872902110053899)
        ·
          refine ⟨263168052487309353165080849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 175445368324872902110053899 263168052487309353165080849)
          ·
            refine ⟨197376039365482014873810637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 263168052487309353165080849 197376039365482014873810637)
            ·
              refine ⟨74016014762055755577678989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 197376039365482014873810637 74016014762055755577678989)
              ·
                refine ⟨27756005535770908341629621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 74016014762055755577678989 27756005535770908341629621)
                ·
                  refine ⟨2602125518978522657027777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 27756005535770908341629621 2602125518978522657027777)
                  ·
                    refine ⟨1951594139233891992770833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2602125518978522657027777 1951594139233891992770833)
                    ·
                      refine ⟨1463695604425418994578125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1951594139233891992770833 1463695604425418994578125)
                      ·
                        rfl

theorem cell23_2850537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 3, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 3, 5, 2, 2].length) (baseStart_2850537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2850537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2850537 prefixEnd_2850537 := by exact prefixLift 2850537
  have htrace : WordTrace (prefixWord ++ tailWord_2850537) baseStart_2850537 baseEnd_2850537 := by
    simpa [prefixWord, tailWord_2850537, baseEnd_2850537] using wordTrace_append hprefix tailTrace_2850537
  have hstable : (prefixWord ++ tailWord_2850537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2850537).length < 2 ^ (prefixWord ++ tailWord_2850537).sum := by decide
  have hdescent : baseEnd_2850537 < baseStart_2850537 := by decide
  rcases family_descends (prefixWord ++ tailWord_2850537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2850543 : List Nat := [1, 1, 2, 1, 5, 1, 1, 11]
def baseStart_2850543 : Nat := 118140960795 + 2850543 * 2 ^ 59
def prefixEnd_2850543 : Nat := 4983230072969 + 3 ^ 40 * 2850543 * 2
def baseEnd_2850543 : Nat := 54211062418864665596411

theorem tailTrace_2850543 : CollatzResearch.WordTrace tailWord_2850543 prefixEnd_2850543 54211062418864665596411 := by
  unfold tailWord_2850543
  simp only [CollatzResearch.WordTrace]
  refine ⟨103967844511977019830676283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69311896341318013220450855 103967844511977019830676283)
  ·
    refine ⟨155951766767965529746014425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103967844511977019830676283 155951766767965529746014425)
    ·
      refine ⟨116963825075974147309510819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 155951766767965529746014425 116963825075974147309510819)
      ·
        refine ⟨175445737613961220964266229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116963825075974147309510819 175445737613961220964266229)
        ·
          refine ⟨16448037901308864465399959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 175445737613961220964266229 16448037901308864465399959)
          ·
            refine ⟨24672056851963296698099939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16448037901308864465399959 24672056851963296698099939)
            ·
              refine ⟨37008085277944945047149909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24672056851963296698099939 37008085277944945047149909)
              ·
                refine ⟨54211062418864665596411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 37008085277944945047149909 54211062418864665596411)
                ·
                  rfl

theorem cell23_2850543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 11].length) (baseStart_2850543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2850543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2850543 prefixEnd_2850543 := by exact prefixLift 2850543
  have htrace : WordTrace (prefixWord ++ tailWord_2850543) baseStart_2850543 baseEnd_2850543 := by
    simpa [prefixWord, tailWord_2850543, baseEnd_2850543] using wordTrace_append hprefix tailTrace_2850543
  have hstable : (prefixWord ++ tailWord_2850543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2850543).length < 2 ^ (prefixWord ++ tailWord_2850543).sum := by decide
  have hdescent : baseEnd_2850543 < baseStart_2850543 := by decide
  rcases family_descends (prefixWord ++ tailWord_2850543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2850564 : List Nat := [2, 3, 2, 2, 1, 3, 2, 2, 2, 4]
def baseStart_2850564 : Nat := 118140960795 + 2850564 * 2 ^ 59
def prefixEnd_2850564 : Nat := 4983230072969 + 3 ^ 40 * 2850564 * 2
def baseEnd_2850564 : Nat := 487903156134363462980167

theorem tailTrace_2850564 : CollatzResearch.WordTrace tailWord_2850564 prefixEnd_2850564 487903156134363462980167 := by
  unfold tailWord_2850564
  simp only [CollatzResearch.WordTrace]
  refine ⟨51984305222450470208595373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69312406963267293611460497 51984305222450470208595373)
  ·
    refine ⟨19494114458418926328223265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51984305222450470208595373 19494114458418926328223265)
    ·
      refine ⟨14620585843814194746167449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19494114458418926328223265 14620585843814194746167449)
      ·
        refine ⟨10965439382860646059625587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14620585843814194746167449 10965439382860646059625587)
        ·
          refine ⟨16448159074290969089438381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10965439382860646059625587 16448159074290969089438381)
          ·
            refine ⟨6168059652859113408539393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16448159074290969089438381 6168059652859113408539393)
            ·
              refine ⟨4626044739644335056404545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6168059652859113408539393 4626044739644335056404545)
              ·
                refine ⟨3469533554733251292303409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4626044739644335056404545 3469533554733251292303409)
                ·
                  refine ⟨2602150166049938469227557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3469533554733251292303409 2602150166049938469227557)
                  ·
                    refine ⟨487903156134363462980167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2602150166049938469227557 487903156134363462980167)
                    ·
                      rfl

theorem cell23_2850564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 2, 2, 2, 4].length) (baseStart_2850564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2850564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2850564 prefixEnd_2850564 := by exact prefixLift 2850564
  have htrace : WordTrace (prefixWord ++ tailWord_2850564) baseStart_2850564 baseEnd_2850564 := by
    simpa [prefixWord, tailWord_2850564, baseEnd_2850564] using wordTrace_append hprefix tailTrace_2850564
  have hstable : (prefixWord ++ tailWord_2850564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2850564).length < 2 ^ (prefixWord ++ tailWord_2850564).sum := by decide
  have hdescent : baseEnd_2850564 < baseStart_2850564 := by decide
  rcases family_descends (prefixWord ++ tailWord_2850564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2850620 : List Nat := [2, 2, 2, 2, 1, 1, 3, 2, 2, 6]
def baseStart_2850620 : Nat := 118140960795 + 2850620 * 2 ^ 59
def prefixEnd_2850620 : Nat := 4983230072969 + 3 ^ 40 * 2850620 * 2
def baseEnd_2850620 : Nat := 487912741106580723280081

theorem tailTrace_2850620 : CollatzResearch.WordTrace tailWord_2850620 prefixEnd_2850620 487912741106580723280081 := by
  unfold tailWord_2850620
  simp only [CollatzResearch.WordTrace]
  refine ⟨51985326466349030990614657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69313768621798707987486209 51985326466349030990614657)
  ·
    refine ⟨38988994849761773242960993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51985326466349030990614657 38988994849761773242960993)
    ·
      refine ⟨29241746137321329932220745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38988994849761773242960993 29241746137321329932220745)
      ·
        refine ⟨21931309602990997449165559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29241746137321329932220745 21931309602990997449165559)
        ·
          refine ⟨32896964404486496173748339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21931309602990997449165559 32896964404486496173748339)
          ·
            refine ⟨49345446606729744260622509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32896964404486496173748339 49345446606729744260622509)
            ·
              refine ⟨18504542477523654097733441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49345446606729744260622509 18504542477523654097733441)
              ·
                refine ⟨13878406858142740573300081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18504542477523654097733441 13878406858142740573300081)
                ·
                  refine ⟨10408805143607055429975061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13878406858142740573300081 10408805143607055429975061)
                  ·
                    refine ⟨487912741106580723280081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10408805143607055429975061 487912741106580723280081)
                    ·
                      rfl

theorem cell23_2850620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 3, 2, 2, 6].length) (baseStart_2850620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2850620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2850620 prefixEnd_2850620 := by exact prefixLift 2850620
  have htrace : WordTrace (prefixWord ++ tailWord_2850620) baseStart_2850620 baseEnd_2850620 := by
    simpa [prefixWord, tailWord_2850620, baseEnd_2850620] using wordTrace_append hprefix tailTrace_2850620
  have hstable : (prefixWord ++ tailWord_2850620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2850620).length < 2 ^ (prefixWord ++ tailWord_2850620).sum := by decide
  have hdescent : baseEnd_2850620 < baseStart_2850620 := by decide
  rcases family_descends (prefixWord ++ tailWord_2850620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2850621 : List Nat := [1, 4, 1, 4, 1, 1, 3, 2, 2, 1, 3]
def baseStart_2850621 : Nat := 118140960795 + 2850621 * 2 ^ 59
def prefixEnd_2850621 : Nat := 4983230072969 + 3 ^ 40 * 2850621 * 2
def baseEnd_2850621 : Nat := 1463738736800396665927739

theorem tailTrace_2850621 : CollatzResearch.WordTrace tailWord_2850621 prefixEnd_2850621 1463738736800396665927739 := by
  unfold tailWord_2850621
  simp only [CollatzResearch.WordTrace]
  refine ⟨103970689405694439152015717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69313792937129626101343811 103970689405694439152015717)
  ·
    refine ⟨19494504263567707341002947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 103970689405694439152015717 19494504263567707341002947)
    ·
      refine ⟨29241756395351561011504421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19494504263567707341002947 29241756395351561011504421)
      ·
        refine ⟨5482829324128417689657079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29241756395351561011504421 5482829324128417689657079)
        ·
          refine ⟨8224243986192626534485619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5482829324128417689657079 8224243986192626534485619)
          ·
            refine ⟨12336365979288939801728429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8224243986192626534485619 12336365979288939801728429)
            ·
              refine ⟨4626137242233352425648161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12336365979288939801728429 4626137242233352425648161)
              ·
                refine ⟨3469602931675014319236121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4626137242233352425648161 3469602931675014319236121)
                ·
                  refine ⟨2602202198756260739427091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3469602931675014319236121 2602202198756260739427091)
                  ·
                    refine ⟨3903303298134391109140637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2602202198756260739427091 3903303298134391109140637)
                    ·
                      refine ⟨1463738736800396665927739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3903303298134391109140637 1463738736800396665927739)
                      ·
                        rfl

theorem cell23_2850621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 3, 2, 2, 1, 3].length) (baseStart_2850621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2850621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2850621 prefixEnd_2850621 := by exact prefixLift 2850621
  have htrace : WordTrace (prefixWord ++ tailWord_2850621) baseStart_2850621 baseEnd_2850621 := by
    simpa [prefixWord, tailWord_2850621, baseEnd_2850621] using wordTrace_append hprefix tailTrace_2850621
  have hstable : (prefixWord ++ tailWord_2850621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2850621).length < 2 ^ (prefixWord ++ tailWord_2850621).sum := by decide
  have hdescent : baseEnd_2850621 < baseStart_2850621 := by decide
  rcases family_descends (prefixWord ++ tailWord_2850621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2850650 : List Nat := [3, 1, 1, 2, 1, 3, 1, 4, 7]
def baseStart_2850650 : Nat := 118140960795 + 2850650 * 2 ^ 59
def prefixEnd_2850650 : Nat := 4983230072969 + 3 ^ 40 * 2850650 * 2
def baseEnd_2850650 : Nat := 162639291971041894718345

theorem tailTrace_2850650 : CollatzResearch.WordTrace tailWord_2850650 prefixEnd_2850650 162639291971041894718345 := by
  unfold tailWord_2850650
  simp only [CollatzResearch.WordTrace]
  refine ⟨25992936780647344276205351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69314498081726251403214269 25992936780647344276205351)
  ·
    refine ⟨38989405170971016414308027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25992936780647344276205351 38989405170971016414308027)
    ·
      refine ⟨58484107756456524621462041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38989405170971016414308027 58484107756456524621462041)
      ·
        refine ⟨43863080817342393466096531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58484107756456524621462041 43863080817342393466096531)
        ·
          refine ⟨65794621226013590199144797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43863080817342393466096531 65794621226013590199144797)
          ·
            refine ⟨24672982959755096324679299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 65794621226013590199144797 24672982959755096324679299)
            ·
              refine ⟨37009474439632644487018949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24672982959755096324679299 37009474439632644487018949)
              ·
                refine ⟨6939276457431120841316053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37009474439632644487018949 6939276457431120841316053)
                ·
                  refine ⟨162639291971041894718345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6939276457431120841316053 162639291971041894718345)
                  ·
                    rfl

theorem cell23_2850650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 4, 7].length) (baseStart_2850650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2850650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2850650 prefixEnd_2850650 := by exact prefixLift 2850650
  have htrace : WordTrace (prefixWord ++ tailWord_2850650) baseStart_2850650 baseEnd_2850650 := by
    simpa [prefixWord, tailWord_2850650, baseEnd_2850650] using wordTrace_append hprefix tailTrace_2850650
  have hstable : (prefixWord ++ tailWord_2850650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2850650).length < 2 ^ (prefixWord ++ tailWord_2850650).sum := by decide
  have hdescent : baseEnd_2850650 < baseStart_2850650 := by decide
  rcases family_descends (prefixWord ++ tailWord_2850650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2850687 : List Nat := [1, 1, 2, 2, 1, 1, 3, 3, 2, 5, 2]
def baseStart_2850687 : Nat := 118140960795 + 2850687 * 2 ^ 59
def prefixEnd_2850687 : Nat := 4983230072969 + 3 ^ 40 * 2850687 * 2
def baseEnd_2850687 : Nat := 1463772626523593407702435

theorem tailTrace_2850687 : CollatzResearch.WordTrace tailWord_2850687 prefixEnd_2850687 1463772626523593407702435 := by
  unfold tailWord_2850687
  simp only [CollatzResearch.WordTrace]
  refine ⟨103973096623455332423918315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69315397748970221615945543 103973096623455332423918315)
  ·
    refine ⟨155959644935182998635877473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103973096623455332423918315 155959644935182998635877473)
    ·
      refine ⟨116969733701387248976908105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 155959644935182998635877473 116969733701387248976908105)
      ·
        refine ⟨87727300276040436732681079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 116969733701387248976908105 87727300276040436732681079)
        ·
          refine ⟨131590950414060655099021619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87727300276040436732681079 131590950414060655099021619)
          ·
            refine ⟨197386425621090982648532429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 131590950414060655099021619 197386425621090982648532429)
            ·
              refine ⟨74019909607909118493199661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 197386425621090982648532429 74019909607909118493199661)
              ·
                refine ⟨27757466102965919434949873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 74019909607909118493199661 27757466102965919434949873)
                ·
                  refine ⟨20818099577224439576212405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27757466102965919434949873 20818099577224439576212405)
                  ·
                    refine ⟨1951696835364791210269913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 20818099577224439576212405 1951696835364791210269913)
                    ·
                      refine ⟨1463772626523593407702435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1951696835364791210269913 1463772626523593407702435)
                      ·
                        rfl

theorem cell23_2850687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 3, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 3, 2, 5, 2].length) (baseStart_2850687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2850687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2850687 prefixEnd_2850687 := by exact prefixLift 2850687
  have htrace : WordTrace (prefixWord ++ tailWord_2850687) baseStart_2850687 baseEnd_2850687 := by
    simpa [prefixWord, tailWord_2850687, baseEnd_2850687] using wordTrace_append hprefix tailTrace_2850687
  have hstable : (prefixWord ++ tailWord_2850687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2850687).length < 2 ^ (prefixWord ++ tailWord_2850687).sum := by decide
  have hdescent : baseEnd_2850687 < baseStart_2850687 := by decide
  rcases family_descends (prefixWord ++ tailWord_2850687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2850695 : List Nat := [1, 1, 4, 2, 4, 2, 2, 1, 2, 2, 2]
def baseStart_2850695 : Nat := 118140960795 + 2850695 * 2 ^ 59
def prefixEnd_2850695 : Nat := 4983230072969 + 3 ^ 40 * 2850695 * 2
def baseEnd_2850695 : Nat := 1463776734368829376402399

theorem tailTrace_2850695 : CollatzResearch.WordTrace tailWord_2850695 prefixEnd_2850695 1463776734368829376402399 := by
  unfold tailWord_2850695
  simp only [CollatzResearch.WordTrace]
  refine ⟨103973388407426349790209539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69315592271617566526806359 103973388407426349790209539)
  ·
    refine ⟨155960082611139524685314309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103973388407426349790209539 155960082611139524685314309)
    ·
      refine ⟨29242515489588660878496433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 155960082611139524685314309 29242515489588660878496433)
      ·
        refine ⟨21931886617191495658872325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29242515489588660878496433 21931886617191495658872325)
        ·
          refine ⟨4112228740723405436038561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21931886617191495658872325 4112228740723405436038561)
          ·
            refine ⟨3084171555542554077028921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4112228740723405436038561 3084171555542554077028921)
            ·
              refine ⟨2313128666656915557771691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3084171555542554077028921 2313128666656915557771691)
              ·
                refine ⟨3469692999985373336657537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2313128666656915557771691 3469692999985373336657537)
                ·
                  refine ⟨2602269749989030002493153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3469692999985373336657537 2602269749989030002493153)
                  ·
                    refine ⟨1951702312491772501869865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2602269749989030002493153 1951702312491772501869865)
                    ·
                      refine ⟨1463776734368829376402399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1951702312491772501869865 1463776734368829376402399)
                      ·
                        rfl

theorem cell23_2850695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 2, 2, 1, 2, 2, 2].length) (baseStart_2850695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2850695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2850695 prefixEnd_2850695 := by exact prefixLift 2850695
  have htrace : WordTrace (prefixWord ++ tailWord_2850695) baseStart_2850695 baseEnd_2850695 := by
    simpa [prefixWord, tailWord_2850695, baseEnd_2850695] using wordTrace_append hprefix tailTrace_2850695
  have hstable : (prefixWord ++ tailWord_2850695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2850695).length < 2 ^ (prefixWord ++ tailWord_2850695).sum := by decide
  have hdescent : baseEnd_2850695 < baseStart_2850695 := by decide
  rcases family_descends (prefixWord ++ tailWord_2850695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2850714 : List Nat := [3, 1, 1, 4, 2, 2, 2, 1, 2, 5]
def baseStart_2850714 : Nat := 118140960795 + 2850714 * 2 ^ 59
def prefixEnd_2850714 : Nat := 4983230072969 + 3 ^ 40 * 2850714 * 2
def baseEnd_2850714 : Nat := 487928830167088267354937

theorem tailTrace_2850714 : CollatzResearch.WordTrace tailWord_2850714 prefixEnd_2850714 487928830167088267354937 := by
  unfold tailWord_2850714
  simp only [CollatzResearch.WordTrace]
  refine ⟨25993520348589379008787799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69316054262905010690100797 25993520348589379008787799)
  ·
    refine ⟨38990280522884068513181699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25993520348589379008787799 38990280522884068513181699)
    ·
      refine ⟨58485420784326102769772549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38990280522884068513181699 58485420784326102769772549)
      ·
        refine ⟨10966016397061144269332353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 58485420784326102769772549 10966016397061144269332353)
        ·
          refine ⟨8224512297795858201999265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10966016397061144269332353 8224512297795858201999265)
          ·
            refine ⟨6168384223346893651499449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8224512297795858201999265 6168384223346893651499449)
            ·
              refine ⟨4626288167510170238624587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6168384223346893651499449 4626288167510170238624587)
              ·
                refine ⟨6939432251265255357936881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4626288167510170238624587 6939432251265255357936881)
                ·
                  refine ⟨5204574188448941518452661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6939432251265255357936881 5204574188448941518452661)
                  ·
                    refine ⟨487928830167088267354937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5204574188448941518452661 487928830167088267354937)
                    ·
                      rfl

theorem cell23_2850714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 2, 1, 2, 5].length) (baseStart_2850714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2850714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2850714 prefixEnd_2850714 := by exact prefixLift 2850714
  have htrace : WordTrace (prefixWord ++ tailWord_2850714) baseStart_2850714 baseEnd_2850714 := by
    simpa [prefixWord, tailWord_2850714, baseEnd_2850714] using wordTrace_append hprefix tailTrace_2850714
  have hstable : (prefixWord ++ tailWord_2850714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2850714).length < 2 ^ (prefixWord ++ tailWord_2850714).sum := by decide
  have hdescent : baseEnd_2850714 < baseStart_2850714 := by decide
  rcases family_descends (prefixWord ++ tailWord_2850714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2850778 : List Nat := [3, 1, 1, 2, 5, 1, 2, 3, 1, 4]
def baseStart_2850778 : Nat := 118140960795 + 2850778 * 2 ^ 59
def prefixEnd_2850778 : Nat := 4983230072969 + 3 ^ 40 * 2850778 * 2
def baseEnd_2850778 : Nat := 487939784421050850554839

theorem tailTrace_2850778 : CollatzResearch.WordTrace tailWord_2850778 prefixEnd_2850778 487939784421050850554839 := by
  unfold tailWord_2850778
  simp only [CollatzResearch.WordTrace]
  refine ⟨25994103916531413741370247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69317610444083769976987325 25994103916531413741370247)
  ·
    refine ⟨38991155874797120612055371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25994103916531413741370247 38991155874797120612055371)
    ·
      refine ⟨58486733812195680918083057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38991155874797120612055371 58486733812195680918083057)
      ·
        refine ⟨43865050359146760688562293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58486733812195680918083057 43865050359146760688562293)
        ·
          refine ⟨4112348471170008814552715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 43865050359146760688562293 4112348471170008814552715)
          ·
            refine ⟨6168522706755013221829073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4112348471170008814552715 6168522706755013221829073)
            ·
              refine ⟨4626392030066259916371805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6168522706755013221829073 4626392030066259916371805)
              ·
                refine ⟨1734897011274847468639427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4626392030066259916371805 1734897011274847468639427)
                ·
                  refine ⟨2602345516912271202959141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1734897011274847468639427 2602345516912271202959141)
                  ·
                    refine ⟨487939784421050850554839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2602345516912271202959141 487939784421050850554839)
                    ·
                      rfl

theorem cell23_2850778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 2, 3, 1, 4].length) (baseStart_2850778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2850778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2850778 prefixEnd_2850778 := by exact prefixLift 2850778
  have htrace : WordTrace (prefixWord ++ tailWord_2850778) baseStart_2850778 baseEnd_2850778 := by
    simpa [prefixWord, tailWord_2850778, baseEnd_2850778] using wordTrace_append hprefix tailTrace_2850778
  have hstable : (prefixWord ++ tailWord_2850778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2850778).length < 2 ^ (prefixWord ++ tailWord_2850778).sum := by decide
  have hdescent : baseEnd_2850778 < baseStart_2850778 := by decide
  rcases family_descends (prefixWord ++ tailWord_2850778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2850791 : List Nat := [1, 1, 5, 2, 3, 2, 1, 2, 6]
def baseStart_2850791 : Nat := 118140960795 + 2850791 * 2 ^ 59
def prefixEnd_2850791 : Nat := 4983230072969 + 3 ^ 40 * 2850791 * 2
def baseEnd_2850791 : Nat := 162647336501295666755773

theorem tailTrace_2850791 : CollatzResearch.WordTrace tailWord_2850791 prefixEnd_2850791 162647336501295666755773 := by
  unfold tailWord_2850791
  simp only [CollatzResearch.WordTrace]
  refine ⟨103976889815078558185704227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69317926543385705457136151 103976889815078558185704227)
  ·
    refine ⟨155965334722617837278556341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103976889815078558185704227 155965334722617837278556341)
    ·
      refine ⟨14621750130245422244864657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 155965334722617837278556341 14621750130245422244864657)
      ·
        refine ⟨10966312597684066683648493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14621750130245422244864657 10966312597684066683648493)
        ·
          refine ⟨4112367224131525006368185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10966312597684066683648493 4112367224131525006368185)
          ·
            refine ⟨3084275418098643754776139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4112367224131525006368185 3084275418098643754776139)
            ·
              refine ⟨4626413127147965632164209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3084275418098643754776139 4626413127147965632164209)
              ·
                refine ⟨3469809845360974224123157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4626413127147965632164209 3469809845360974224123157)
                ·
                  refine ⟨162647336501295666755773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3469809845360974224123157 162647336501295666755773)
                  ·
                    rfl

theorem cell23_2850791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 2, 1, 2, 6].length) (baseStart_2850791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2850791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2850791 prefixEnd_2850791 := by exact prefixLift 2850791
  have htrace : WordTrace (prefixWord ++ tailWord_2850791) baseStart_2850791 baseEnd_2850791 := by
    simpa [prefixWord, tailWord_2850791, baseEnd_2850791] using wordTrace_append hprefix tailTrace_2850791
  have hstable : (prefixWord ++ tailWord_2850791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2850791).length < 2 ^ (prefixWord ++ tailWord_2850791).sum := by decide
  have hdescent : baseEnd_2850791 < baseStart_2850791 := by decide
  rcases family_descends (prefixWord ++ tailWord_2850791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2850824 : List Nat := [2, 1, 3, 2, 1, 2, 1, 1, 2, 6, 2]
def baseStart_2850824 : Nat := 118140960795 + 2850824 * 2 ^ 59
def prefixEnd_2850824 : Nat := 4983230072969 + 3 ^ 40 * 2850824 * 2
def baseEnd_2850824 : Nat := 1463842973373259371689305

theorem tailTrace_2850824 : CollatzResearch.WordTrace tailWord_2850824 prefixEnd_2850824 1463842973373259371689305 := by
  unfold tailWord_2850824
  simp only [CollatzResearch.WordTrace]
  refine ⟨51989046711979502410827763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69318728949306003214437017 51989046711979502410827763)
  ·
    refine ⟨77983570067969253616241645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51989046711979502410827763 77983570067969253616241645)
    ·
      refine ⟨29243838775488470106090617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 77983570067969253616241645 29243838775488470106090617)
      ·
        refine ⟨21932879081616352579567963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29243838775488470106090617 21932879081616352579567963)
        ·
          refine ⟨32899318622424528869351945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21932879081616352579567963 32899318622424528869351945)
          ·
            refine ⟨24674488966818396652013959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32899318622424528869351945 24674488966818396652013959)
            ·
              refine ⟨37011733450227594978020939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24674488966818396652013959 37011733450227594978020939)
              ·
                refine ⟨55517600175341392467031409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37011733450227594978020939 55517600175341392467031409)
                ·
                  refine ⟨41638200131506044350273557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 55517600175341392467031409 41638200131506044350273557)
                  ·
                    refine ⟨1951790631164345828919073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 41638200131506044350273557 1951790631164345828919073)
                    ·
                      refine ⟨1463842973373259371689305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1951790631164345828919073 1463842973373259371689305)
                      ·
                        rfl

theorem cell23_2850824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 1, 2, 6, 2].length) (baseStart_2850824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2850824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2850824 prefixEnd_2850824 := by exact prefixLift 2850824
  have htrace : WordTrace (prefixWord ++ tailWord_2850824) baseStart_2850824 baseEnd_2850824 := by
    simpa [prefixWord, tailWord_2850824, baseEnd_2850824] using wordTrace_append hprefix tailTrace_2850824
  have hstable : (prefixWord ++ tailWord_2850824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2850824).length < 2 ^ (prefixWord ++ tailWord_2850824).sum := by decide
  have hdescent : baseEnd_2850824 < baseStart_2850824 := by decide
  rcases family_descends (prefixWord ++ tailWord_2850824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2850827 : List Nat := [1, 1, 1, 1, 6, 1, 1, 2, 3, 1, 5]
def baseStart_2850827 : Nat := 118140960795 + 2850827 * 2 ^ 59
def prefixEnd_2850827 : Nat := 4983230072969 + 3 ^ 40 * 2850827 * 2
def baseEnd_2850827 : Nat := 1463844513815222859951791

theorem tailTrace_2850827 : CollatzResearch.WordTrace tailWord_2850827 prefixEnd_2850827 1463844513815222859951791 := by
  unfold tailWord_2850827
  simp only [CollatzResearch.WordTrace]
  refine ⟨103978202842948136334014735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69318801895298757556009823 103978202842948136334014735)
  ·
    refine ⟨155967304264422204501022103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103978202842948136334014735 155967304264422204501022103)
    ·
      refine ⟨233950956396633306751533155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155967304264422204501022103 233950956396633306751533155)
      ·
        refine ⟨350926434594949960127299733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 233950956396633306751533155 350926434594949960127299733)
        ·
          refine ⟨16449676621638279380967175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 350926434594949960127299733 16449676621638279380967175)
          ·
            refine ⟨24674514932457419071450763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16449676621638279380967175 24674514932457419071450763)
            ·
              refine ⟨37011772398686128607176145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24674514932457419071450763 37011772398686128607176145)
              ·
                refine ⟨27758829299014596455382109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37011772398686128607176145 27758829299014596455382109)
                ·
                  refine ⟨10409560987130473670768291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27758829299014596455382109 10409560987130473670768291)
                  ·
                    refine ⟨15614341480695710506152437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10409560987130473670768291 15614341480695710506152437)
                    ·
                      refine ⟨1463844513815222859951791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15614341480695710506152437 1463844513815222859951791)
                      ·
                        rfl

theorem cell23_2850827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 2, 3, 1, 5].length) (baseStart_2850827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2850827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2850827 prefixEnd_2850827 := by exact prefixLift 2850827
  have htrace : WordTrace (prefixWord ++ tailWord_2850827) baseStart_2850827 baseEnd_2850827 := by
    simpa [prefixWord, tailWord_2850827, baseEnd_2850827] using wordTrace_append hprefix tailTrace_2850827
  have hstable : (prefixWord ++ tailWord_2850827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2850827).length < 2 ^ (prefixWord ++ tailWord_2850827).sum := by decide
  have hdescent : baseEnd_2850827 < baseStart_2850827 := by decide
  rcases family_descends (prefixWord ++ tailWord_2850827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2850829 : List Nat := [1, 7, 1, 2, 1, 2, 1, 3, 1, 4]
def baseStart_2850829 : Nat := 118140960795 + 2850829 * 2 ^ 59
def prefixEnd_2850829 : Nat := 4983230072969 + 3 ^ 40 * 2850829 * 2
def baseEnd_2850829 : Nat := 487948513592177284042261

theorem tailTrace_2850829 : CollatzResearch.WordTrace tailWord_2850829 prefixEnd_2850829 487948513592177284042261 := by
  unfold tailWord_2850829
  simp only [CollatzResearch.WordTrace]
  refine ⟨103978275788940890675587541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69318850525960593783725027 103978275788940890675587541)
  ·
    refine ⟨2436990838803302125209083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 103978275788940890675587541 2436990838803302125209083)
    ·
      refine ⟨3655486258204953187813625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2436990838803302125209083 3655486258204953187813625)
      ·
        refine ⟨2741614693653714890860219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3655486258204953187813625 2741614693653714890860219)
        ·
          refine ⟨4112422040480572336290329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2741614693653714890860219 4112422040480572336290329)
          ·
            refine ⟨3084316530360429252217747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4112422040480572336290329 3084316530360429252217747)
            ·
              refine ⟨4626474795540643878326621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3084316530360429252217747 4626474795540643878326621)
              ·
                refine ⟨1734928048327741454372483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4626474795540643878326621 1734928048327741454372483)
                ·
                  refine ⟨2602392072491612181558725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1734928048327741454372483 2602392072491612181558725)
                  ·
                    refine ⟨487948513592177284042261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2602392072491612181558725 487948513592177284042261)
                    ·
                      rfl

theorem cell23_2850829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 2, 1, 3, 1, 4].length) (baseStart_2850829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2850829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2850829 prefixEnd_2850829 := by exact prefixLift 2850829
  have htrace : WordTrace (prefixWord ++ tailWord_2850829) baseStart_2850829 baseEnd_2850829 := by
    simpa [prefixWord, tailWord_2850829, baseEnd_2850829] using wordTrace_append hprefix tailTrace_2850829
  have hstable : (prefixWord ++ tailWord_2850829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2850829).length < 2 ^ (prefixWord ++ tailWord_2850829).sum := by decide
  have hdescent : baseEnd_2850829 < baseStart_2850829 := by decide
  rcases family_descends (prefixWord ++ tailWord_2850829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2850844 : List Nat := [2, 2, 3, 1, 3, 1, 1, 3, 1, 1, 5]
def baseStart_2850844 : Nat := 118140960795 + 2850844 * 2 ^ 59
def prefixEnd_2850844 : Nat := 4983230072969 + 3 ^ 40 * 2850844 * 2
def baseEnd_2850844 : Nat := 1463853242986349293439213

theorem tailTrace_2850844 : CollatzResearch.WordTrace tailWord_2850844 prefixEnd_2850844 1463853242986349293439213 := by
  unfold tailWord_2850844
  simp only [CollatzResearch.WordTrace]
  refine ⟨51989411441943274118691793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69319215255924365491589057 51989411441943274118691793)
  ·
    refine ⟨38992058581457455589018845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51989411441943274118691793 38992058581457455589018845)
    ·
      refine ⟨14622021968046545845882067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38992058581457455589018845 14622021968046545845882067)
      ·
        refine ⟨21933032952069818768823101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14622021968046545845882067 21933032952069818768823101)
        ·
          refine ⟨8224887357026182038308663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21933032952069818768823101 8224887357026182038308663)
          ·
            refine ⟨12337331035539273057462995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8224887357026182038308663 12337331035539273057462995)
            ·
              refine ⟨18505996553308909586194493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12337331035539273057462995 18505996553308909586194493)
              ·
                refine ⟨6939748707490841094822935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18505996553308909586194493 6939748707490841094822935)
                ·
                  refine ⟨10409623061236261642234403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6939748707490841094822935 10409623061236261642234403)
                  ·
                    refine ⟨15614434591854392463351605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10409623061236261642234403 15614434591854392463351605)
                    ·
                      refine ⟨1463853242986349293439213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15614434591854392463351605 1463853242986349293439213)
                      ·
                        rfl

theorem cell23_2850844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 1, 3, 1, 1, 5].length) (baseStart_2850844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2850844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2850844 prefixEnd_2850844 := by exact prefixLift 2850844
  have htrace : WordTrace (prefixWord ++ tailWord_2850844) baseStart_2850844 baseEnd_2850844 := by
    simpa [prefixWord, tailWord_2850844, baseEnd_2850844] using wordTrace_append hprefix tailTrace_2850844
  have hstable : (prefixWord ++ tailWord_2850844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2850844).length < 2 ^ (prefixWord ++ tailWord_2850844).sum := by decide
  have hdescent : baseEnd_2850844 < baseStart_2850844 := by decide
  rcases family_descends (prefixWord ++ tailWord_2850844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2850852 : List Nat := [2, 3, 1, 4, 2, 1, 3, 2, 1, 1, 3]
def baseStart_2850852 : Nat := 118140960795 + 2850852 * 2 ^ 59
def prefixEnd_2850852 : Nat := 4983230072969 + 3 ^ 40 * 2850852 * 2
def baseEnd_2850852 : Nat := 1463857350831585262139177

theorem tailTrace_2850852 : CollatzResearch.WordTrace tailWord_2850852 prefixEnd_2850852 1463857350831585262139177 := by
  unfold tailWord_2850852
  simp only [CollatzResearch.WordTrace]
  refine ⟨51989557333928782801837405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69319409778571710402449873 51989557333928782801837405)
  ·
    refine ⟨19496084000223293550689027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51989557333928782801837405 19496084000223293550689027)
    ·
      refine ⟨29244126000334940326033541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19496084000223293550689027 29244126000334940326033541)
      ·
        refine ⟨5483273625062801311131289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29244126000334940326033541 5483273625062801311131289)
        ·
          refine ⟨4112455218797100983348467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5483273625062801311131289 4112455218797100983348467)
          ·
            refine ⟨6168682828195651475022701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4112455218797100983348467 6168682828195651475022701)
            ·
              refine ⟨2313256060573369303133513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6168682828195651475022701 2313256060573369303133513)
              ·
                refine ⟨1734942045430026977350135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2313256060573369303133513 1734942045430026977350135)
                ·
                  refine ⟨2602413068145040466025203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1734942045430026977350135 2602413068145040466025203)
                  ·
                    refine ⟨3903619602217560699037805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2602413068145040466025203 3903619602217560699037805)
                    ·
                      refine ⟨1463857350831585262139177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3903619602217560699037805 1463857350831585262139177)
                      ·
                        rfl

theorem cell23_2850852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 3, 2, 1, 1, 3].length) (baseStart_2850852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2850852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2850852 prefixEnd_2850852 := by exact prefixLift 2850852
  have htrace : WordTrace (prefixWord ++ tailWord_2850852) baseStart_2850852 baseEnd_2850852 := by
    simpa [prefixWord, tailWord_2850852, baseEnd_2850852] using wordTrace_append hprefix tailTrace_2850852
  have hstable : (prefixWord ++ tailWord_2850852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2850852).length < 2 ^ (prefixWord ++ tailWord_2850852).sum := by decide
  have hdescent : baseEnd_2850852 < baseStart_2850852 := by decide
  rcases family_descends (prefixWord ++ tailWord_2850852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2850874 : List Nat := [3, 1, 1, 1, 3, 1, 1, 5, 1, 3, 3]
def baseStart_2850874 : Nat := 118140960795 + 2850874 * 2 ^ 59
def prefixEnd_2850874 : Nat := 4983230072969 + 3 ^ 40 * 2850874 * 2
def baseEnd_2850874 : Nat := 1463868647405984176064075

theorem tailTrace_2850874 : CollatzResearch.WordTrace tailWord_2850874 prefixEnd_2850874 1463868647405984176064075 := by
  unfold tailWord_2850874
  simp only [CollatzResearch.WordTrace]
  refine ⟨25994979268444465840243919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69319944715851908907317117 25994979268444465840243919)
  ·
    refine ⟨38992468902666698760365879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25994979268444465840243919 38992468902666698760365879)
    ·
      refine ⟨58488703354000048140548819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38992468902666698760365879 58488703354000048140548819)
      ·
        refine ⟨87733055031000072210823229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58488703354000048140548819 87733055031000072210823229)
        ·
          refine ⟨32899895636625027079058711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 87733055031000072210823229 32899895636625027079058711)
          ·
            refine ⟨49349843454937540618588067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32899895636625027079058711 49349843454937540618588067)
            ·
              refine ⟨74024765182406310927882101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49349843454937540618588067 74024765182406310927882101)
              ·
                refine ⟨6939821735850591649488947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 74024765182406310927882101 6939821735850591649488947)
                ·
                  refine ⟨10409732603775887474233421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6939821735850591649488947 10409732603775887474233421)
                  ·
                    refine ⟨3903649726415957802837533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10409732603775887474233421 3903649726415957802837533)
                    ·
                      refine ⟨1463868647405984176064075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3903649726415957802837533 1463868647405984176064075)
                      ·
                        rfl

theorem cell23_2850874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 5, 1, 3, 3].length) (baseStart_2850874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2850874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2850874 prefixEnd_2850874 := by exact prefixLift 2850874
  have htrace : WordTrace (prefixWord ++ tailWord_2850874) baseStart_2850874 baseEnd_2850874 := by
    simpa [prefixWord, tailWord_2850874, baseEnd_2850874] using wordTrace_append hprefix tailTrace_2850874
  have hstable : (prefixWord ++ tailWord_2850874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2850874).length < 2 ^ (prefixWord ++ tailWord_2850874).sum := by decide
  have hdescent : baseEnd_2850874 < baseStart_2850874 := by decide
  rcases family_descends (prefixWord ++ tailWord_2850874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2850878 : List Nat := [4, 2, 1, 3, 2, 1, 1, 1, 3, 2, 3]
def baseStart_2850878 : Nat := 118140960795 + 2850878 * 2 ^ 59
def prefixEnd_2850878 : Nat := 4983230072969 + 3 ^ 40 * 2850878 * 2
def baseEnd_2850878 : Nat := 1463870701328602160414057

theorem tailTrace_2850878 : CollatzResearch.WordTrace tailWord_2850878 prefixEnd_2850878 1463870701328602160414057 := by
  unfold tailWord_2850878
  simp only [CollatzResearch.WordTrace]
  refine ⟨12997507870720421505515161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 69320041977175581362747525 12997507870720421505515161)
  ·
    refine ⟨9748130903040316129136371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12997507870720421505515161 9748130903040316129136371)
    ·
      refine ⟨14622196354560474193704557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9748130903040316129136371 14622196354560474193704557)
      ·
        refine ⟨5483323632960177822639209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14622196354560474193704557 5483323632960177822639209)
        ·
          refine ⟨4112492724720133366979407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5483323632960177822639209 4112492724720133366979407)
          ·
            refine ⟨6168739087080200050469111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4112492724720133366979407 6168739087080200050469111)
            ·
              refine ⟨9253108630620300075703667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6168739087080200050469111 9253108630620300075703667)
              ·
                refine ⟨13879662945930450113555501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9253108630620300075703667 13879662945930450113555501)
                ·
                  refine ⟨5204873604723918792583313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13879662945930450113555501 5204873604723918792583313)
                  ·
                    refine ⟨3903655203542939094437485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5204873604723918792583313 3903655203542939094437485)
                    ·
                      refine ⟨1463870701328602160414057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3903655203542939094437485 1463870701328602160414057)
                      ·
                        rfl

theorem cell23_2850878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 1, 1, 3, 2, 3].length) (baseStart_2850878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2850878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2850878 prefixEnd_2850878 := by exact prefixLift 2850878
  have htrace : WordTrace (prefixWord ++ tailWord_2850878) baseStart_2850878 baseEnd_2850878 := by
    simpa [prefixWord, tailWord_2850878, baseEnd_2850878] using wordTrace_append hprefix tailTrace_2850878
  have hstable : (prefixWord ++ tailWord_2850878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2850878).length < 2 ^ (prefixWord ++ tailWord_2850878).sum := by decide
  have hdescent : baseEnd_2850878 < baseStart_2850878 := by decide
  rcases family_descends (prefixWord ++ tailWord_2850878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2850908 : List Nat := [2, 2, 4, 1, 1, 2, 1, 4, 2, 1, 3]
def baseStart_2850908 : Nat := 118140960795 + 2850908 * 2 ^ 59
def prefixEnd_2850908 : Nat := 4983230072969 + 3 ^ 40 * 2850908 * 2
def baseEnd_2850908 : Nat := 1463886105748237043038919

theorem tailTrace_2850908 : CollatzResearch.WordTrace tailWord_2850908 prefixEnd_2850908 1463886105748237043038919 := by
  unfold tailWord_2850908
  simp only [CollatzResearch.WordTrace]
  refine ⟨51990578577827343583856689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69320771437103124778475585 51990578577827343583856689)
  ·
    refine ⟨38992933933370507687892517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51990578577827343583856689 38992933933370507687892517)
    ·
      refine ⟨7311175112506970191479847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 38992933933370507687892517 7311175112506970191479847)
      ·
        refine ⟨10966762668760455287219771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7311175112506970191479847 10966762668760455287219771)
        ·
          refine ⟨16450144003140682930829657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10966762668760455287219771 16450144003140682930829657)
          ·
            refine ⟨12337608002355512198122243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16450144003140682930829657 12337608002355512198122243)
            ·
              refine ⟨18506412003533268297183365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12337608002355512198122243 18506412003533268297183365)
              ·
                refine ⟨3469952250662487805721881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18506412003533268297183365 3469952250662487805721881)
                ·
                  refine ⟨2602464187996865854291411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3469952250662487805721881 2602464187996865854291411)
                  ·
                    refine ⟨3903696281995298781437117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2602464187996865854291411 3903696281995298781437117)
                    ·
                      refine ⟨1463886105748237043038919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3903696281995298781437117 1463886105748237043038919)
                      ·
                        rfl

theorem cell23_2850908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 1, 4, 2, 1, 3].length) (baseStart_2850908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2850908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2850908 prefixEnd_2850908 := by exact prefixLift 2850908
  have htrace : WordTrace (prefixWord ++ tailWord_2850908) baseStart_2850908 baseEnd_2850908 := by
    simpa [prefixWord, tailWord_2850908, baseEnd_2850908] using wordTrace_append hprefix tailTrace_2850908
  have hstable : (prefixWord ++ tailWord_2850908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2850908).length < 2 ^ (prefixWord ++ tailWord_2850908).sum := by decide
  have hdescent : baseEnd_2850908 < baseStart_2850908 := by decide
  rcases family_descends (prefixWord ++ tailWord_2850908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2850909 : List Nat := [1, 4, 4, 1, 1, 1, 4, 2, 1, 2, 2]
def baseStart_2850909 : Nat := 118140960795 + 2850909 * 2 ^ 59
def prefixEnd_2850909 : Nat := 4983230072969 + 3 ^ 40 * 2850909 * 2
def baseEnd_2850909 : Nat := 1463886619228891539126415

theorem tailTrace_2850909 : CollatzResearch.WordTrace tailWord_2850909 prefixEnd_2850909 1463886619228891539126415 := by
  unfold tailWord_2850909
  simp only [CollatzResearch.WordTrace]
  refine ⟨103981193628651064338499781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69320795752434042892333187 103981193628651064338499781)
  ·
    refine ⟨19496473805372074563468709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 103981193628651064338499781 19496473805372074563468709)
    ·
      refine ⟨3655588838507263980650383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19496473805372074563468709 3655588838507263980650383)
      ·
        refine ⟨5483383257760895970975575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3655588838507263980650383 5483383257760895970975575)
        ·
          refine ⟨8225074886641343956463363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5483383257760895970975575 8225074886641343956463363)
          ·
            refine ⟨12337612329962015934695045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8225074886641343956463363 12337612329962015934695045)
            ·
              refine ⟨2313302311867877987755321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12337612329962015934695045 2313302311867877987755321)
              ·
                refine ⟨1734976733900908490816491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2313302311867877987755321 1734976733900908490816491)
                ·
                  refine ⟨2602465100851362736224737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1734976733900908490816491 2602465100851362736224737)
                  ·
                    refine ⟨1951848825638522052168553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2602465100851362736224737 1951848825638522052168553)
                    ·
                      refine ⟨1463886619228891539126415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1951848825638522052168553 1463886619228891539126415)
                      ·
                        rfl

theorem cell23_2850909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 4, 2, 1, 2, 2].length) (baseStart_2850909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2850909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2850909 prefixEnd_2850909 := by exact prefixLift 2850909
  have htrace : WordTrace (prefixWord ++ tailWord_2850909) baseStart_2850909 baseEnd_2850909 := by
    simpa [prefixWord, tailWord_2850909, baseEnd_2850909] using wordTrace_append hprefix tailTrace_2850909
  have hstable : (prefixWord ++ tailWord_2850909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2850909).length < 2 ^ (prefixWord ++ tailWord_2850909).sum := by decide
  have hdescent : baseEnd_2850909 < baseStart_2850909 := by decide
  rcases family_descends (prefixWord ++ tailWord_2850909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2850924 : List Nat := [2, 2, 1, 1, 3, 4, 1, 1, 2, 6]
def baseStart_2850924 : Nat := 118140960795 + 2850924 * 2 ^ 59
def prefixEnd_2850924 : Nat := 4983230072969 + 3 ^ 40 * 2850924 * 2
def baseEnd_2850924 : Nat := 487964773812902993479615

theorem tailTrace_2850924 : CollatzResearch.WordTrace tailWord_2850924 prefixEnd_2850924 487964773812902993479615 := by
  unfold tailWord_2850924
  simp only [CollatzResearch.WordTrace]
  refine ⟨51990870361798360950147913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69321160482397814600197217 51990870361798360950147913)
  ·
    refine ⟨38993152771348770712610935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51990870361798360950147913 38993152771348770712610935)
    ·
      refine ⟨58489729157023156068916403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38993152771348770712610935 58489729157023156068916403)
      ·
        refine ⟨87734593735534734103374605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58489729157023156068916403 87734593735534734103374605)
        ·
          refine ⟨32900472650825525288765477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 87734593735534734103374605 32900472650825525288765477)
          ·
            refine ⟨6168838622029785991643527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32900472650825525288765477 6168838622029785991643527)
            ·
              refine ⟨9253257933044678987465291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6168838622029785991643527 9253257933044678987465291)
              ·
                refine ⟨13879886899567018481197937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9253257933044678987465291 13879886899567018481197937)
                ·
                  refine ⟨10409915174675263860898453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13879886899567018481197937 10409915174675263860898453)
                  ·
                    refine ⟨487964773812902993479615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10409915174675263860898453 487964773812902993479615)
                    ·
                      rfl

theorem cell23_2850924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 6].length) (baseStart_2850924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2850924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2850924 prefixEnd_2850924 := by exact prefixLift 2850924
  have htrace : WordTrace (prefixWord ++ tailWord_2850924) baseStart_2850924 baseEnd_2850924 := by
    simpa [prefixWord, tailWord_2850924, baseEnd_2850924] using wordTrace_append hprefix tailTrace_2850924
  have hstable : (prefixWord ++ tailWord_2850924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2850924).length < 2 ^ (prefixWord ++ tailWord_2850924).sum := by decide
  have hdescent : baseEnd_2850924 < baseStart_2850924 := by decide
  rcases family_descends (prefixWord ++ tailWord_2850924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2850948 : List Nat := [2, 3, 2, 1, 2, 1, 2, 2, 4, 2, 2]
def baseStart_2850948 : Nat := 118140960795 + 2850948 * 2 ^ 59
def prefixEnd_2850948 : Nat := 4983230072969 + 3 ^ 40 * 2850948 * 2
def baseEnd_2850948 : Nat := 1463906644974416886538735

theorem tailTrace_2850948 : CollatzResearch.WordTrace tailWord_2850948 prefixEnd_2850948 1463906644974416886538735 := by
  unfold tailWord_2850948
  simp only [CollatzResearch.WordTrace]
  refine ⟨51991308037754886999584749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69321744050339849332779665 51991308037754886999584749)
  ·
    refine ⟨19496740514158082624844281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51991308037754886999584749 19496740514158082624844281)
    ·
      refine ⟨14622555385618561968633211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19496740514158082624844281 14622555385618561968633211)
      ·
        refine ⟨21933833078427842952949817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14622555385618561968633211 21933833078427842952949817)
        ·
          refine ⟨16450374808820882214712363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21933833078427842952949817 16450374808820882214712363)
          ·
            refine ⟨24675562213231323322068545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16450374808820882214712363 24675562213231323322068545)
            ·
              refine ⟨18506671659923492491551409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24675562213231323322068545 18506671659923492491551409)
              ·
                refine ⟨13880003744942619368663557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18506671659923492491551409 13880003744942619368663557)
                ·
                  refine ⟨2602500702176741131624417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13880003744942619368663557 2602500702176741131624417)
                  ·
                    refine ⟨1951875526632555848718313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2602500702176741131624417 1951875526632555848718313)
                    ·
                      refine ⟨1463906644974416886538735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1951875526632555848718313 1463906644974416886538735)
                      ·
                        rfl

theorem cell23_2850948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 2, 2, 4, 2, 2].length) (baseStart_2850948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2850948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2850948 prefixEnd_2850948 := by exact prefixLift 2850948
  have htrace : WordTrace (prefixWord ++ tailWord_2850948) baseStart_2850948 baseEnd_2850948 := by
    simpa [prefixWord, tailWord_2850948, baseEnd_2850948] using wordTrace_append hprefix tailTrace_2850948
  have hstable : (prefixWord ++ tailWord_2850948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2850948).length < 2 ^ (prefixWord ++ tailWord_2850948).sum := by decide
  have hdescent : baseEnd_2850948 < baseStart_2850948 := by decide
  rcases family_descends (prefixWord ++ tailWord_2850948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2850952 : List Nat := [2, 1, 3, 4, 1, 3, 2, 1, 1, 3, 2]
def baseStart_2850952 : Nat := 118140960795 + 2850952 * 2 ^ 59
def prefixEnd_2850952 : Nat := 4983230072969 + 3 ^ 40 * 2850952 * 2
def baseEnd_2850952 : Nat := 1463908698897034870888717

theorem tailTrace_2850952 : CollatzResearch.WordTrace tailWord_2850952 prefixEnd_2850952 1463908698897034870888717 := by
  unfold tailWord_2850952
  simp only [CollatzResearch.WordTrace]
  refine ⟨51991380983747641341157555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69321841311663521788210073 51991380983747641341157555)
  ·
    refine ⟨77987071475621462011736333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51991380983747641341157555 77987071475621462011736333)
    ·
      refine ⟨29245151803358048254401125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 77987071475621462011736333 29245151803358048254401125)
      ·
        refine ⟨5483465963129634047700211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29245151803358048254401125 5483465963129634047700211)
        ·
          refine ⟨8225198944694451071550317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5483465963129634047700211 8225198944694451071550317)
          ·
            refine ⟨3084449604260419151831369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8225198944694451071550317 3084449604260419151831369)
            ·
              refine ⟨2313337203195314363873527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3084449604260419151831369 2313337203195314363873527)
              ·
                refine ⟨3470005804792971545810291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2313337203195314363873527 3470005804792971545810291)
                ·
                  refine ⟨5205008707189457318715437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3470005804792971545810291 5205008707189457318715437)
                  ·
                    refine ⟨1951878265196046494518289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5205008707189457318715437 1951878265196046494518289)
                    ·
                      refine ⟨1463908698897034870888717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1951878265196046494518289 1463908698897034870888717)
                      ·
                        rfl

theorem cell23_2850952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 3, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 3, 2, 1, 1, 3, 2].length) (baseStart_2850952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2850952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2850952 prefixEnd_2850952 := by exact prefixLift 2850952
  have htrace : WordTrace (prefixWord ++ tailWord_2850952) baseStart_2850952 baseEnd_2850952 := by
    simpa [prefixWord, tailWord_2850952, baseEnd_2850952] using wordTrace_append hprefix tailTrace_2850952
  have hstable : (prefixWord ++ tailWord_2850952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2850952).length < 2 ^ (prefixWord ++ tailWord_2850952).sum := by decide
  have hdescent : baseEnd_2850952 < baseStart_2850952 := by decide
  rcases family_descends (prefixWord ++ tailWord_2850952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2851024 : List Nat := [2, 1, 1, 1, 1, 2, 1, 1, 2, 8, 3]
def baseStart_2851024 : Nat := 118140960795 + 2851024 * 2 ^ 59
def prefixEnd_2851024 : Nat := 4983230072969 + 3 ^ 40 * 2851024 * 2
def baseEnd_2851024 : Nat := 1463945669504158589188385

theorem tailTrace_2851024 : CollatzResearch.WordTrace tailWord_2851024 prefixEnd_2851024 1463945669504158589188385 := by
  unfold tailWord_2851024
  simp only [CollatzResearch.WordTrace]
  refine ⟨51992694011617219489468063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69323592015489625985957417 51992694011617219489468063)
  ·
    refine ⟨77989041017425829234202095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51992694011617219489468063 77989041017425829234202095)
    ·
      refine ⟨116983561526138743851303143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77989041017425829234202095 116983561526138743851303143)
      ·
        refine ⟨175475342289208115776954715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116983561526138743851303143 175475342289208115776954715)
        ·
          refine ⟨263213013433812173665432073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 175475342289208115776954715 263213013433812173665432073)
          ·
            refine ⟨197409760075359130249074055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 263213013433812173665432073 197409760075359130249074055)
            ·
              refine ⟨296114640113038695373611083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 197409760075359130249074055 296114640113038695373611083)
              ·
                refine ⟨444171960169558043060416625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 296114640113038695373611083 444171960169558043060416625)
                ·
                  refine ⟨333128970127168532295312469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 444171960169558043060416625 333128970127168532295312469)
                  ·
                    refine ⟨3903855118677756237835693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 333128970127168532295312469 3903855118677756237835693)
                    ·
                      refine ⟨1463945669504158589188385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3903855118677756237835693 1463945669504158589188385)
                      ·
                        rfl

theorem cell23_2851024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 2, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 2, 8, 3].length) (baseStart_2851024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2851024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2851024 prefixEnd_2851024 := by exact prefixLift 2851024
  have htrace : WordTrace (prefixWord ++ tailWord_2851024) baseStart_2851024 baseEnd_2851024 := by
    simpa [prefixWord, tailWord_2851024, baseEnd_2851024] using wordTrace_append hprefix tailTrace_2851024
  have hstable : (prefixWord ++ tailWord_2851024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2851024).length < 2 ^ (prefixWord ++ tailWord_2851024).sum := by decide
  have hdescent : baseEnd_2851024 < baseStart_2851024 := by decide
  rcases family_descends (prefixWord ++ tailWord_2851024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2851034 : List Nat := [3, 1, 1, 2, 2, 1, 2, 2, 2, 1, 6]
def baseStart_2851034 : Nat := 118140960795 + 2851034 * 2 ^ 59
def prefixEnd_2851034 : Nat := 4983230072969 + 3 ^ 40 * 2851034 * 2
def baseEnd_2851034 : Nat := 1463950804310703550063339

theorem tailTrace_2851034 : CollatzResearch.WordTrace tailWord_2851034 prefixEnd_2851034 1463950804310703550063339 := by
  unfold tailWord_2851034
  simp only [CollatzResearch.WordTrace]
  refine ⟨25996438188299552671700039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69323835168798807124533437 25996438188299552671700039)
  ·
    refine ⟨38994657282449329007550059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25996438188299552671700039 38994657282449329007550059)
    ·
      refine ⟨58491985923673993511325089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38994657282449329007550059 58491985923673993511325089)
      ·
        refine ⟨43868989442755495133493817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58491985923673993511325089 43868989442755495133493817)
        ·
          refine ⟨32901742082066621350120363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43868989442755495133493817 32901742082066621350120363)
          ·
            refine ⟨49352613123099932025180545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32901742082066621350120363 49352613123099932025180545)
            ·
              refine ⟨37014459842324949018885409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49352613123099932025180545 37014459842324949018885409)
              ·
                refine ⟨27760844881743711764164057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37014459842324949018885409 27760844881743711764164057)
                ·
                  refine ⟨20820633661307783823123043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27760844881743711764164057 20820633661307783823123043)
                  ·
                    refine ⟨31230950491961675734684565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20820633661307783823123043 31230950491961675734684565)
                    ·
                      refine ⟨1463950804310703550063339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 31230950491961675734684565 1463950804310703550063339)
                      ·
                        rfl

theorem cell23_2851034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 2, 2, 1, 6].length) (baseStart_2851034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2851034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2851034 prefixEnd_2851034 := by exact prefixLift 2851034
  have htrace : WordTrace (prefixWord ++ tailWord_2851034) baseStart_2851034 baseEnd_2851034 := by
    simpa [prefixWord, tailWord_2851034, baseEnd_2851034] using wordTrace_append hprefix tailTrace_2851034
  have hstable : (prefixWord ++ tailWord_2851034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2851034).length < 2 ^ (prefixWord ++ tailWord_2851034).sum := by decide
  have hdescent : baseEnd_2851034 < baseStart_2851034 := by decide
  rcases family_descends (prefixWord ++ tailWord_2851034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2851041 : List Nat := [1, 2, 3, 1, 3, 1, 1, 2, 4, 2, 3]
def baseStart_2851041 : Nat := 118140960795 + 2851041 * 2 ^ 59
def prefixEnd_2851041 : Nat := 4983230072969 + 3 ^ 40 * 2851041 * 2
def baseEnd_2851041 : Nat := 1463954398675285022675807

theorem tailTrace_2851041 : CollatzResearch.WordTrace tailWord_2851041 prefixEnd_2851041 1463954398675285022675807 := by
  unfold tailWord_2851041
  simp only [CollatzResearch.WordTrace]
  refine ⟨103986008064172850882304977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69324005376115233921536651 103986008064172850882304977)
  ·
    refine ⟨77989506048129638161728733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103986008064172850882304977 77989506048129638161728733)
    ·
      refine ⟨29246064768048614310648275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 77989506048129638161728733 29246064768048614310648275)
      ·
        refine ⟨43869097152072921465972413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29246064768048614310648275 43869097152072921465972413)
        ·
          refine ⟨16450911432027345549739655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43869097152072921465972413 16450911432027345549739655)
          ·
            refine ⟨24676367148041018324609483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16450911432027345549739655 24676367148041018324609483)
            ·
              refine ⟨37014550722061527486914225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24676367148041018324609483 37014550722061527486914225)
              ·
                refine ⟨27760913041546145615185669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37014550722061527486914225 27760913041546145615185669)
                ·
                  refine ⟨5205171195289902302847313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27760913041546145615185669 5205171195289902302847313)
                  ·
                    refine ⟨3903878396467426727135485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5205171195289902302847313 3903878396467426727135485)
                    ·
                      refine ⟨1463954398675285022675807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3903878396467426727135485 1463954398675285022675807)
                      ·
                        rfl

theorem cell23_2851041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 2, 4, 2, 3].length) (baseStart_2851041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2851041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2851041 prefixEnd_2851041 := by exact prefixLift 2851041
  have htrace : WordTrace (prefixWord ++ tailWord_2851041) baseStart_2851041 baseEnd_2851041 := by
    simpa [prefixWord, tailWord_2851041, baseEnd_2851041] using wordTrace_append hprefix tailTrace_2851041
  have hstable : (prefixWord ++ tailWord_2851041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2851041).length < 2 ^ (prefixWord ++ tailWord_2851041).sum := by decide
  have hdescent : baseEnd_2851041 < baseStart_2851041 := by decide
  rcases family_descends (prefixWord ++ tailWord_2851041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2851058 : List Nat := [3, 2, 1, 3, 2, 1, 1, 3, 2, 2, 3]
def baseStart_2851058 : Nat := 118140960795 + 2851058 * 2 ^ 59
def prefixEnd_2851058 : Nat := 4983230072969 + 3 ^ 40 * 2851058 * 2
def baseEnd_2851058 : Nat := 1463963127846411456163229

theorem tailTrace_2851058 : CollatzResearch.WordTrace tailWord_2851058 prefixEnd_2851058 1463963127846411456163229 := by
  unfold tailWord_2851058
  simp only [CollatzResearch.WordTrace]
  refine ⟨25996657026277815696418457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69324418736740841857115885 25996657026277815696418457)
  ·
    refine ⟨19497492769708361772313843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25996657026277815696418457 19497492769708361772313843)
    ·
      refine ⟨29246239154562542658470765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19497492769708361772313843 29246239154562542658470765)
      ·
        refine ⟨10967339682960953496926537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29246239154562542658470765 10967339682960953496926537)
        ·
          refine ⟨8225504762220715122694903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10967339682960953496926537 8225504762220715122694903)
          ·
            refine ⟨12338257143331072684042355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8225504762220715122694903 12338257143331072684042355)
            ·
              refine ⟨18507385714996609026063533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12338257143331072684042355 18507385714996609026063533)
              ·
                refine ⟨6940269643123728384773825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18507385714996609026063533 6940269643123728384773825)
                ·
                  refine ⟨5205202232342796288580369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6940269643123728384773825 5205202232342796288580369)
                  ·
                    refine ⟨3903901674257097216435277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5205202232342796288580369 3903901674257097216435277)
                    ·
                      refine ⟨1463963127846411456163229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3903901674257097216435277 1463963127846411456163229)
                      ·
                        rfl

theorem cell23_2851058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 1, 3, 2, 2, 3].length) (baseStart_2851058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2851058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2851058 prefixEnd_2851058 := by exact prefixLift 2851058
  have htrace : WordTrace (prefixWord ++ tailWord_2851058) baseStart_2851058 baseEnd_2851058 := by
    simpa [prefixWord, tailWord_2851058, baseEnd_2851058] using wordTrace_append hprefix tailTrace_2851058
  have hstable : (prefixWord ++ tailWord_2851058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2851058).length < 2 ^ (prefixWord ++ tailWord_2851058).sum := by decide
  have hdescent : baseEnd_2851058 < baseStart_2851058 := by decide
  rcases family_descends (prefixWord ++ tailWord_2851058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2851212 : List Nat := [2, 2, 1, 2, 1, 4, 4, 1, 2, 1, 3]
def baseStart_2851212 : Nat := 118140960795 + 2851212 * 2 ^ 59
def prefixEnd_2851212 : Nat := 4983230072969 + 3 ^ 40 * 2851212 * 2
def baseEnd_2851212 : Nat := 1464042203867203853637521

theorem tailTrace_2851212 : CollatzResearch.WordTrace tailWord_2851212 prefixEnd_2851212 1464042203867203853637521 := by
  unfold tailWord_2851212
  simp only [CollatzResearch.WordTrace]
  refine ⟨51996122473276673543389945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69328163297702231391186593 51996122473276673543389945)
  ·
    refine ⟨38997091854957505157542459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51996122473276673543389945 38997091854957505157542459)
    ·
      refine ⟨58495637782436257736313689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38997091854957505157542459 58495637782436257736313689)
      ·
        refine ⟨43871728336827193302235267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58495637782436257736313689 43871728336827193302235267)
        ·
          refine ⟨65807592505240789953352901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43871728336827193302235267 65807592505240789953352901)
          ·
            refine ⟨12338923594732648116253669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 65807592505240789953352901 12338923594732648116253669)
            ·
              refine ⟨2313548174012371521797563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12338923594732648116253669 2313548174012371521797563)
              ·
                refine ⟨3470322261018557282696345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2313548174012371521797563 3470322261018557282696345)
                ·
                  refine ⟨2602741695763917962022259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3470322261018557282696345 2602741695763917962022259)
                  ·
                    refine ⟨3904112543645876943033389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2602741695763917962022259 3904112543645876943033389)
                    ·
                      refine ⟨1464042203867203853637521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3904112543645876943033389 1464042203867203853637521)
                      ·
                        rfl

theorem cell23_2851212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 4, 1, 2, 1, 3].length) (baseStart_2851212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2851212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2851212 prefixEnd_2851212 := by exact prefixLift 2851212
  have htrace : WordTrace (prefixWord ++ tailWord_2851212) baseStart_2851212 baseEnd_2851212 := by
    simpa [prefixWord, tailWord_2851212, baseEnd_2851212] using wordTrace_append hprefix tailTrace_2851212
  have hstable : (prefixWord ++ tailWord_2851212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2851212).length < 2 ^ (prefixWord ++ tailWord_2851212).sum := by decide
  have hdescent : baseEnd_2851212 < baseStart_2851212 := by decide
  rcases family_descends (prefixWord ++ tailWord_2851212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2851235 : List Nat := [1, 1, 1, 4, 1, 5, 1, 2, 1, 4, 2]
def baseStart_2851235 : Nat := 118140960795 + 2851235 * 2 ^ 59
def prefixEnd_2851235 : Nat := 4983230072969 + 3 ^ 40 * 2851235 * 2
def baseEnd_2851235 : Nat := 1464054013922257263649915

theorem tailTrace_2851235 : CollatzResearch.WordTrace tailWord_2851235 prefixEnd_2851235 1464054013922257263649915 := by
  unfold tailWord_2851235
  simp only [CollatzResearch.WordTrace]
  refine ⟨103993083825470022014867159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69328722550313348009911439 103993083825470022014867159)
  ·
    refine ⟨155989625738205033022300739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103993083825470022014867159 155989625738205033022300739)
    ·
      refine ⟨233984438607307549533451109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155989625738205033022300739 233984438607307549533451109)
      ·
        refine ⟨43872082238870165537522083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 233984438607307549533451109 43872082238870165537522083)
        ·
          refine ⟨65808123358305248306283125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43872082238870165537522083 65808123358305248306283125)
          ·
            refine ⟨6169511564841117028714043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 65808123358305248306283125 6169511564841117028714043)
            ·
              refine ⟨9254267347261675543071065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6169511564841117028714043 9254267347261675543071065)
              ·
                refine ⟨6940700510446256657303299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9254267347261675543071065 6940700510446256657303299)
                ·
                  refine ⟨10411050765669384985954949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6940700510446256657303299 10411050765669384985954949)
                  ·
                    refine ⟨1952072018563009684866553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10411050765669384985954949 1952072018563009684866553)
                    ·
                      refine ⟨1464054013922257263649915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1952072018563009684866553 1464054013922257263649915)
                      ·
                        rfl

theorem cell23_2851235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 1, 2, 1, 4, 2].length) (baseStart_2851235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2851235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2851235 prefixEnd_2851235 := by exact prefixLift 2851235
  have htrace : WordTrace (prefixWord ++ tailWord_2851235) baseStart_2851235 baseEnd_2851235 := by
    simpa [prefixWord, tailWord_2851235, baseEnd_2851235] using wordTrace_append hprefix tailTrace_2851235
  have hstable : (prefixWord ++ tailWord_2851235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2851235).length < 2 ^ (prefixWord ++ tailWord_2851235).sum := by decide
  have hdescent : baseEnd_2851235 < baseStart_2851235 := by decide
  rcases family_descends (prefixWord ++ tailWord_2851235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2851239 : List Nat := [1, 1, 6, 1, 1, 3, 3, 1, 1, 3, 2]
def baseStart_2851239 : Nat := 118140960795 + 2851239 * 2 ^ 59
def prefixEnd_2851239 : Nat := 4983230072969 + 3 ^ 40 * 2851239 * 2
def baseEnd_2851239 : Nat := 1464056067844875247999897

theorem tailTrace_2851239 : CollatzResearch.WordTrace tailWord_2851239 prefixEnd_2851239 1464056067844875247999897 := by
  unfold tailWord_2851239
  simp only [CollatzResearch.WordTrace]
  refine ⟨103993229717455530698012771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69328819811637020465341847 103993229717455530698012771)
  ·
    refine ⟨155989844576183296047019157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103993229717455530698012771 155989844576183296047019157)
    ·
      refine ⟨7312023964508592002204023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 155989844576183296047019157 7312023964508592002204023)
      ·
        refine ⟨10968035946762888003306035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7312023964508592002204023 10968035946762888003306035)
        ·
          refine ⟨16452053920144332004959053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10968035946762888003306035 16452053920144332004959053)
          ·
            refine ⟨6169520220054124501859645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16452053920144332004959053 6169520220054124501859645)
            ·
              refine ⟨2313570082520296688197367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6169520220054124501859645 2313570082520296688197367)
              ·
                refine ⟨3470355123780445032296051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2313570082520296688197367 3470355123780445032296051)
                ·
                  refine ⟨5205532685670667548444077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3470355123780445032296051 5205532685670667548444077)
                  ·
                    refine ⟨1952074757126500330666529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5205532685670667548444077 1952074757126500330666529)
                    ·
                      refine ⟨1464056067844875247999897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1952074757126500330666529 1464056067844875247999897)
                      ·
                        rfl

theorem cell23_2851239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 3, 1, 1, 3, 2].length) (baseStart_2851239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2851239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2851239 prefixEnd_2851239 := by exact prefixLift 2851239
  have htrace : WordTrace (prefixWord ++ tailWord_2851239) baseStart_2851239 baseEnd_2851239 := by
    simpa [prefixWord, tailWord_2851239, baseEnd_2851239] using wordTrace_append hprefix tailTrace_2851239
  have hstable : (prefixWord ++ tailWord_2851239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2851239).length < 2 ^ (prefixWord ++ tailWord_2851239).sum := by decide
  have hdescent : baseEnd_2851239 < baseStart_2851239 := by decide
  rcases family_descends (prefixWord ++ tailWord_2851239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
