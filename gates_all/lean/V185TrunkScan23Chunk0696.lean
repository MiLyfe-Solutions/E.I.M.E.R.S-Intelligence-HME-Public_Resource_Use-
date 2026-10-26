import V185TrunkScan23Chunk0695

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_4114183 : List Nat := [1, 1, 4, 4, 2, 1, 1, 3, 1, 1, 4]
def baseStart_4114183 : Nat := 118140960795 + 4114183 * 2 ^ 59
def prefixEnd_4114183 : Nat := 4983230072969 + 3 ^ 40 * 4114183 * 2
def baseEnd_4114183 : Nat := 2112553379556781973791723

theorem tailTrace_4114183 : CollatzResearch.WordTrace tailWord_4114183 prefixEnd_4114183 2112553379556781973791723 := by
  unfold tailWord_4114183
  simp only [CollatzResearch.WordTrace]
  refine ⟨150056581654025112360963203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100037721102683408240642135 150056581654025112360963203)
  ·
    refine ⟨225084872481037668541444805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150056581654025112360963203 225084872481037668541444805)
    ·
      refine ⟨42203413590194562851520901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 225084872481037668541444805 42203413590194562851520901)
      ·
        refine ⟨7913140048161480534660169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42203413590194562851520901 7913140048161480534660169)
        ·
          refine ⟨5934855036121110400995127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7913140048161480534660169 5934855036121110400995127)
          ·
            refine ⟨8902282554181665601492691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5934855036121110400995127 8902282554181665601492691)
            ·
              refine ⟨13353423831272498402239037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8902282554181665601492691 13353423831272498402239037)
              ·
                refine ⟨5007533936727186900839639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13353423831272498402239037 5007533936727186900839639)
                ·
                  refine ⟨7511300905090780351259459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5007533936727186900839639 7511300905090780351259459)
                  ·
                    refine ⟨11266951357636170526889189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7511300905090780351259459 11266951357636170526889189)
                    ·
                      refine ⟨2112553379556781973791723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11266951357636170526889189 2112553379556781973791723)
                      ·
                        rfl

theorem cell23_4114183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 1, 3, 1, 1, 4].length) (baseStart_4114183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4114183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4114183 prefixEnd_4114183 := by exact prefixLift 4114183
  have htrace : WordTrace (prefixWord ++ tailWord_4114183) baseStart_4114183 baseEnd_4114183 := by
    simpa [prefixWord, tailWord_4114183, baseEnd_4114183] using wordTrace_append hprefix tailTrace_4114183
  have hstable : (prefixWord ++ tailWord_4114183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4114183).length < 2 ^ (prefixWord ++ tailWord_4114183).sum := by decide
  have hdescent : baseEnd_4114183 < baseStart_4114183 := by decide
  rcases family_descends (prefixWord ++ tailWord_4114183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4114200 : List Nat := [2, 1, 2, 3, 1, 1, 4, 4, 1, 2, 2]
def baseStart_4114200 : Nat := 118140960795 + 4114200 * 2 ^ 59
def prefixEnd_4114200 : Nat := 4983230072969 + 3 ^ 40 * 4114200 * 2
def baseEnd_4114200 : Nat := 2112562108727908407279145

theorem tailTrace_4114200 : CollatzResearch.WordTrace tailWord_4114200 prefixEnd_4114200 2112562108727908407279145 := by
  unfold tailWord_4114200
  simp only [CollatzResearch.WordTrace]
  refine ⟨75028600847481762132166027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100038134463309016176221369 75028600847481762132166027)
  ·
    refine ⟨112542901271222643198249041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75028600847481762132166027 112542901271222643198249041)
    ·
      refine ⟨84407175953416982398686781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112542901271222643198249041 84407175953416982398686781)
      ·
        refine ⟨31652690982531368399507543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84407175953416982398686781 31652690982531368399507543)
        ·
          refine ⟨47479036473797052599261315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31652690982531368399507543 47479036473797052599261315)
          ·
            refine ⟨71218554710695578898891973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47479036473797052599261315 71218554710695578898891973)
            ·
              refine ⟨13353479008255421043542245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 71218554710695578898891973 13353479008255421043542245)
              ·
                refine ⟨2503777314047891445664171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13353479008255421043542245 2503777314047891445664171)
                ·
                  refine ⟨3755665971071837168496257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2503777314047891445664171 3755665971071837168496257)
                  ·
                    refine ⟨2816749478303877876372193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3755665971071837168496257 2816749478303877876372193)
                    ·
                      refine ⟨2112562108727908407279145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2816749478303877876372193 2112562108727908407279145)
                      ·
                        rfl

theorem cell23_4114200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 4, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 4, 4, 1, 2, 2].length) (baseStart_4114200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4114200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4114200 prefixEnd_4114200 := by exact prefixLift 4114200
  have htrace : WordTrace (prefixWord ++ tailWord_4114200) baseStart_4114200 baseEnd_4114200 := by
    simpa [prefixWord, tailWord_4114200, baseEnd_4114200] using wordTrace_append hprefix tailTrace_4114200
  have hstable : (prefixWord ++ tailWord_4114200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4114200).length < 2 ^ (prefixWord ++ tailWord_4114200).sum := by decide
  have hdescent : baseEnd_4114200 < baseStart_4114200 := by decide
  rcases family_descends (prefixWord ++ tailWord_4114200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4114243 : List Nat := [1, 1, 1, 3, 1, 5, 2, 3, 1, 3, 2]
def baseStart_4114243 : Nat := 118140960795 + 4114243 * 2 ^ 59
def prefixEnd_4114243 : Nat := 4983230072969 + 3 ^ 40 * 4114243 * 2
def baseEnd_4114243 : Nat := 2112584188396051739041447

theorem tailTrace_4114243 : CollatzResearch.WordTrace tailWord_4114243 prefixEnd_4114243 2112584188396051739041447 := by
  unfold tailWord_4114243
  simp only [CollatzResearch.WordTrace]
  refine ⟨150058770033807742608147383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100039180022538495072098255 150058770033807742608147383)
  ·
    refine ⟨225088155050711613912221075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150058770033807742608147383 225088155050711613912221075)
    ·
      refine ⟨337632232576067420868331613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225088155050711613912221075 337632232576067420868331613)
      ·
        refine ⟨126612087216025282825624355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 337632232576067420868331613 126612087216025282825624355)
        ·
          refine ⟨189918130824037924238436533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126612087216025282825624355 189918130824037924238436533)
          ·
            refine ⟨17804824764753555397353425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 189918130824037924238436533 17804824764753555397353425)
            ·
              refine ⟨13353618573565166548015069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17804824764753555397353425 13353618573565166548015069)
              ·
                refine ⟨5007606965086937455505651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13353618573565166548015069 5007606965086937455505651)
                ·
                  refine ⟨7511410447630406183258477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5007606965086937455505651 7511410447630406183258477)
                  ·
                    refine ⟨2816778917861402318721929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7511410447630406183258477 2816778917861402318721929)
                    ·
                      refine ⟨2112584188396051739041447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2816778917861402318721929 2112584188396051739041447)
                      ·
                        rfl

theorem cell23_4114243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 2, 3, 1, 3, 2].length) (baseStart_4114243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4114243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4114243 prefixEnd_4114243 := by exact prefixLift 4114243
  have htrace : WordTrace (prefixWord ++ tailWord_4114243) baseStart_4114243 baseEnd_4114243 := by
    simpa [prefixWord, tailWord_4114243, baseEnd_4114243] using wordTrace_append hprefix tailTrace_4114243
  have hstable : (prefixWord ++ tailWord_4114243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4114243).length < 2 ^ (prefixWord ++ tailWord_4114243).sum := by decide
  have hdescent : baseEnd_4114243 < baseStart_4114243 := by decide
  rcases family_descends (prefixWord ++ tailWord_4114243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4114279 : List Nat := [1, 1, 5, 1, 2, 1, 2, 1, 9]
def baseStart_4114279 : Nat := 118140960795 + 4114279 * 2 ^ 59
def prefixEnd_4114279 : Nat := 4983230072969 + 3 ^ 40 * 4114279 * 2
def baseEnd_4114279 : Nat := 234733630411068177576809

theorem tailTrace_4114279 : CollatzResearch.WordTrace tailWord_4114279 prefixEnd_4114279 234733630411068177576809 := by
  unfold tailWord_4114279
  simp only [CollatzResearch.WordTrace]
  refine ⟨150060083061677320756457891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100040055374451547170971927 150060083061677320756457891)
  ·
    refine ⟨225090124592515981134686837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150060083061677320756457891 225090124592515981134686837)
    ·
      refine ⟨21102199180548373231376891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 225090124592515981134686837 21102199180548373231376891)
      ·
        refine ⟨31653298770822559847065337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21102199180548373231376891 31653298770822559847065337)
        ·
          refine ⟨23739974078116919885299003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31653298770822559847065337 23739974078116919885299003)
          ·
            refine ⟨35609961117175379827948505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23739974078116919885299003 35609961117175379827948505)
            ·
              refine ⟨26707470837881534870961379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35609961117175379827948505 26707470837881534870961379)
              ·
                refine ⟨40061206256822302306442069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26707470837881534870961379 40061206256822302306442069)
                ·
                  refine ⟨234733630411068177576809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 40061206256822302306442069 234733630411068177576809)
                  ·
                    rfl

theorem cell23_4114279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 2, 1, 9].length) (baseStart_4114279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4114279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4114279 prefixEnd_4114279 := by exact prefixLift 4114279
  have htrace : WordTrace (prefixWord ++ tailWord_4114279) baseStart_4114279 baseEnd_4114279 := by
    simpa [prefixWord, tailWord_4114279, baseEnd_4114279] using wordTrace_append hprefix tailTrace_4114279
  have hstable : (prefixWord ++ tailWord_4114279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4114279).length < 2 ^ (prefixWord ++ tailWord_4114279).sum := by decide
  have hdescent : baseEnd_4114279 < baseStart_4114279 := by decide
  rcases family_descends (prefixWord ++ tailWord_4114279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4114294 : List Nat := [5, 1, 1, 3, 2, 1, 3, 1, 1, 3, 2]
def baseStart_4114294 : Nat := 118140960795 + 4114294 * 2 ^ 59
def prefixEnd_4114294 : Nat := 4983230072969 + 3 ^ 40 * 4114294 * 2
def baseEnd_4114294 : Nat := 2112610375909431039503713

theorem tailTrace_4114294 : CollatzResearch.WordTrace tailWord_4114294 prefixEnd_4114294 2112610375909431039503713 := by
  unfold tailWord_4114294
  simp only [CollatzResearch.WordTrace]
  refine ⟨9378789384788936144890871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 100040420104415318878835957 9378789384788936144890871)
  ·
    refine ⟨14068184077183404217336307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9378789384788936144890871 14068184077183404217336307)
    ·
      refine ⟨21102276115775106326004461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14068184077183404217336307 21102276115775106326004461)
      ·
        refine ⟨7913353543415664872251673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21102276115775106326004461 7913353543415664872251673)
        ·
          refine ⟨5935015157561748654188755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7913353543415664872251673 5935015157561748654188755)
          ·
            refine ⟨8902522736342622981283133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5935015157561748654188755 8902522736342622981283133)
            ·
              refine ⟨3338446026128483617981175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8902522736342622981283133 3338446026128483617981175)
              ·
                refine ⟨5007669039192725426971763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3338446026128483617981175 5007669039192725426971763)
                ·
                  refine ⟨7511503558789088140457645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5007669039192725426971763 7511503558789088140457645)
                  ·
                    refine ⟨2816813834545908052671617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7511503558789088140457645 2816813834545908052671617)
                    ·
                      refine ⟨2112610375909431039503713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2816813834545908052671617 2112610375909431039503713)
                      ·
                        rfl

theorem cell23_4114294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 3, 1, 1, 3, 2].length) (baseStart_4114294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4114294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4114294 prefixEnd_4114294 := by exact prefixLift 4114294
  have htrace : WordTrace (prefixWord ++ tailWord_4114294) baseStart_4114294 baseEnd_4114294 := by
    simpa [prefixWord, tailWord_4114294, baseEnd_4114294] using wordTrace_append hprefix tailTrace_4114294
  have hstable : (prefixWord ++ tailWord_4114294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4114294).length < 2 ^ (prefixWord ++ tailWord_4114294).sum := by decide
  have hdescent : baseEnd_4114294 < baseStart_4114294 := by decide
  rcases family_descends (prefixWord ++ tailWord_4114294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4114343 : List Nat := [1, 1, 6, 1, 2, 1, 3, 1, 2, 5]
def baseStart_4114343 : Nat := 118140960795 + 4114343 * 2 ^ 59
def prefixEnd_4114343 : Nat := 4983230072969 + 3 ^ 40 * 4114343 * 2
def baseEnd_4114343 : Nat := 704211845487167115930329

theorem tailTrace_4114343 : CollatzResearch.WordTrace tailWord_4114343 prefixEnd_4114343 704211845487167115930329 := by
  unfold tailWord_4114343
  simp only [CollatzResearch.WordTrace]
  refine ⟨150062417333445459686787683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100041611555630306457858455 150062417333445459686787683)
  ·
    refine ⟨225093626000168189530181525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150062417333445459686787683 225093626000168189530181525)
    ·
      refine ⟨10551263718757883884227259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 225093626000168189530181525 10551263718757883884227259)
      ·
        refine ⟨15826895578136825826340889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10551263718757883884227259 15826895578136825826340889)
        ·
          refine ⟨11870171683602619369755667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15826895578136825826340889 11870171683602619369755667)
          ·
            refine ⟨17805257525403929054633501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11870171683602619369755667 17805257525403929054633501)
            ·
              refine ⟨6676971572026473395487563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17805257525403929054633501 6676971572026473395487563)
              ·
                refine ⟨10015457358039710093231345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6676971572026473395487563 10015457358039710093231345)
                ·
                  refine ⟨7511593018529782569923509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10015457358039710093231345 7511593018529782569923509)
                  ·
                    refine ⟨704211845487167115930329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7511593018529782569923509 704211845487167115930329)
                    ·
                      rfl

theorem cell23_4114343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 3, 1, 2, 5].length) (baseStart_4114343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4114343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4114343 prefixEnd_4114343 := by exact prefixLift 4114343
  have htrace : WordTrace (prefixWord ++ tailWord_4114343) baseStart_4114343 baseEnd_4114343 := by
    simpa [prefixWord, tailWord_4114343, baseEnd_4114343] using wordTrace_append hprefix tailTrace_4114343
  have hstable : (prefixWord ++ tailWord_4114343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4114343).length < 2 ^ (prefixWord ++ tailWord_4114343).sum := by decide
  have hdescent : baseEnd_4114343 < baseStart_4114343 := by decide
  rcases family_descends (prefixWord ++ tailWord_4114343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4114480 : List Nat := [2, 1, 1, 1, 2, 6, 2, 2, 2, 4]
def baseStart_4114480 : Nat := 118140960795 + 4114480 * 2 ^ 59
def prefixEnd_4114480 : Nat := 4983230072969 + 3 ^ 40 * 4114480 * 2
def baseEnd_4114480 : Nat := 704235294437055770592619

theorem tailTrace_4114480 : CollatzResearch.WordTrace tailWord_4114480 prefixEnd_4114480 704235294437055770592619 := by
  unfold tailWord_4114480
  simp only [CollatzResearch.WordTrace]
  refine ⟨75033707066974566042262447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100044942755966088056349929 75033707066974566042262447)
  ·
    refine ⟨112550560600461849063393671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75033707066974566042262447 112550560600461849063393671)
    ·
      refine ⟨168825840900692773595090507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112550560600461849063393671 168825840900692773595090507)
      ·
        refine ⟨253238761351039160392635761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168825840900692773595090507 253238761351039160392635761)
        ·
          refine ⟨189929071013279370294476821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 253238761351039160392635761 189929071013279370294476821)
          ·
            refine ⟨8902925203747470482553601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 189929071013279370294476821 8902925203747470482553601)
            ·
              refine ⟨6677193902810602861915201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8902925203747470482553601 6677193902810602861915201)
              ·
                refine ⟨5007895427107952146436401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6677193902810602861915201 5007895427107952146436401)
                ·
                  refine ⟨3755921570330964109827301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5007895427107952146436401 3755921570330964109827301)
                  ·
                    refine ⟨704235294437055770592619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3755921570330964109827301 704235294437055770592619)
                    ·
                      rfl

theorem cell23_4114480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 2, 2, 2, 4].length) (baseStart_4114480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4114480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4114480 prefixEnd_4114480 := by exact prefixLift 4114480
  have htrace : WordTrace (prefixWord ++ tailWord_4114480) baseStart_4114480 baseEnd_4114480 := by
    simpa [prefixWord, tailWord_4114480, baseEnd_4114480] using wordTrace_append hprefix tailTrace_4114480
  have hstable : (prefixWord ++ tailWord_4114480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4114480).length < 2 ^ (prefixWord ++ tailWord_4114480).sum := by decide
  have hdescent : baseEnd_4114480 < baseStart_4114480 := by decide
  rcases family_descends (prefixWord ++ tailWord_4114480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4114506 : List Nat := [3, 1, 2, 1, 1, 2, 1, 1, 4, 7]
def baseStart_4114506 : Nat := 118140960795 + 4114506 * 2 ^ 59
def prefixEnd_4114506 : Nat := 4983230072969 + 3 ^ 40 * 4114506 * 2
def baseEnd_4114506 : Nat := 704239744602728070017579

theorem tailTrace_4114506 : CollatzResearch.WordTrace tailWord_4114506 prefixEnd_4114506 704239744602728070017579 := by
  unfold tailWord_4114506
  simp only [CollatzResearch.WordTrace]
  refine ⟨37517090607963734631242843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100045574954569959016647581 37517090607963734631242843)
  ·
    refine ⟨56275635911945601946864265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37517090607963734631242843 56275635911945601946864265)
    ·
      refine ⟨42206726933959201460148199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56275635911945601946864265 42206726933959201460148199)
      ·
        refine ⟨63310090400938802190222299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42206726933959201460148199 63310090400938802190222299)
        ·
          refine ⟨94965135601408203285333449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63310090400938802190222299 94965135601408203285333449)
          ·
            refine ⟨71223851701056152464000087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94965135601408203285333449 71223851701056152464000087)
            ·
              refine ⟨106835777551584228696000131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71223851701056152464000087 106835777551584228696000131)
              ·
                refine ⟨160253666327376343044000197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 106835777551584228696000131 160253666327376343044000197)
                ·
                  refine ⟨30047562436383064320750037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 160253666327376343044000197 30047562436383064320750037)
                  ·
                    refine ⟨704239744602728070017579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 30047562436383064320750037 704239744602728070017579)
                    ·
                      rfl

theorem cell23_4114506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 1, 4, 7].length) (baseStart_4114506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4114506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4114506 prefixEnd_4114506 := by exact prefixLift 4114506
  have htrace : WordTrace (prefixWord ++ tailWord_4114506) baseStart_4114506 baseEnd_4114506 := by
    simpa [prefixWord, tailWord_4114506, baseEnd_4114506] using wordTrace_append hprefix tailTrace_4114506
  have hstable : (prefixWord ++ tailWord_4114506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4114506).length < 2 ^ (prefixWord ++ tailWord_4114506).sum := by decide
  have hdescent : baseEnd_4114506 < baseStart_4114506 := by decide
  rcases family_descends (prefixWord ++ tailWord_4114506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4114524 : List Nat := [2, 2, 4, 1, 1, 4, 2, 1, 1, 2, 3]
def baseStart_4114524 : Nat := 118140960795 + 4114524 * 2 ^ 59
def prefixEnd_4114524 : Nat := 4983230072969 + 3 ^ 40 * 4114524 * 2
def baseEnd_4114524 : Nat := 2112728476459965139627655

theorem tailTrace_4114524 : CollatzResearch.WordTrace tailWord_4114524 prefixEnd_4114524 2112728476459965139627655 := by
  unfold tailWord_4114524
  simp only [CollatzResearch.WordTrace]
  refine ⟨75034509472894863799563313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100046012630526485066084417 75034509472894863799563313)
  ·
    refine ⟨56275882104671147849672485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75034509472894863799563313 56275882104671147849672485)
    ·
      refine ⟨10551727894625840221813591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 56275882104671147849672485 10551727894625840221813591)
      ·
        refine ⟨15827591841938760332720387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10551727894625840221813591 15827591841938760332720387)
        ·
          refine ⟨23741387762908140499080581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15827591841938760332720387 23741387762908140499080581)
          ·
            refine ⟨4451510205545276343577609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23741387762908140499080581 4451510205545276343577609)
            ·
              refine ⟨3338632654158957257683207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4451510205545276343577609 3338632654158957257683207)
              ·
                refine ⟨5007948981238435886524811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3338632654158957257683207 5007948981238435886524811)
                ·
                  refine ⟨7511923471857653829787217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5007948981238435886524811 7511923471857653829787217)
                  ·
                    refine ⟨5633942603893240372340413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7511923471857653829787217 5633942603893240372340413)
                    ·
                      refine ⟨2112728476459965139627655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5633942603893240372340413 2112728476459965139627655)
                      ·
                        rfl

theorem cell23_4114524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 4, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 4, 2, 1, 1, 2, 3].length) (baseStart_4114524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4114524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4114524 prefixEnd_4114524 := by exact prefixLift 4114524
  have htrace : WordTrace (prefixWord ++ tailWord_4114524) baseStart_4114524 baseEnd_4114524 := by
    simpa [prefixWord, tailWord_4114524, baseEnd_4114524] using wordTrace_append hprefix tailTrace_4114524
  have hstable : (prefixWord ++ tailWord_4114524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4114524).length < 2 ^ (prefixWord ++ tailWord_4114524).sum := by decide
  have hdescent : baseEnd_4114524 < baseStart_4114524 := by decide
  rcases family_descends (prefixWord ++ tailWord_4114524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4114553 : List Nat := [1, 2, 1, 3, 4, 1, 2, 1, 2, 6]
def baseStart_4114553 : Nat := 118140960795 + 4114553 * 2 ^ 59
def prefixEnd_4114553 : Nat := 4983230072969 + 3 ^ 40 * 4114553 * 2
def baseEnd_4114553 : Nat := 704247789132981842055007

theorem tailTrace_4114553 : CollatzResearch.WordTrace tailWord_4114553 prefixEnd_4114553 704247789132981842055007 := by
  unfold tailWord_4114553
  simp only [CollatzResearch.WordTrace]
  refine ⟨150070076662684665551932313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100046717775123110367954875 150070076662684665551932313)
  ·
    refine ⟨112552557497013499163949235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150070076662684665551932313 112552557497013499163949235)
    ·
      refine ⟨168828836245520248745923853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112552557497013499163949235 168828836245520248745923853)
      ·
        refine ⟨63310813592070093279721445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 168828836245520248745923853 63310813592070093279721445)
        ·
          refine ⟨11870777548513142489947771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 63310813592070093279721445 11870777548513142489947771)
          ·
            refine ⟨17806166322769713734921657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11870777548513142489947771 17806166322769713734921657)
            ·
              refine ⟨13354624742077285301191243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17806166322769713734921657 13354624742077285301191243)
              ·
                refine ⟨20031937113115927951786865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13354624742077285301191243 20031937113115927951786865)
                ·
                  refine ⟨15023952834836945963840149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20031937113115927951786865 15023952834836945963840149)
                  ·
                    refine ⟨704247789132981842055007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15023952834836945963840149 704247789132981842055007)
                    ·
                      rfl

theorem cell23_4114553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 2, 1, 2, 6].length) (baseStart_4114553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4114553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4114553 prefixEnd_4114553 := by exact prefixLift 4114553
  have htrace : WordTrace (prefixWord ++ tailWord_4114553) baseStart_4114553 baseEnd_4114553 := by
    simpa [prefixWord, tailWord_4114553, baseEnd_4114553] using wordTrace_append hprefix tailTrace_4114553
  have hstable : (prefixWord ++ tailWord_4114553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4114553).length < 2 ^ (prefixWord ++ tailWord_4114553).sum := by decide
  have hdescent : baseEnd_4114553 < baseStart_4114553 := by decide
  rcases family_descends (prefixWord ++ tailWord_4114553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4114594 : List Nat := [3, 3, 1, 3, 1, 1, 2, 1, 4, 2, 2]
def baseStart_4114594 : Nat := 118140960795 + 4114594 * 2 ^ 59
def prefixEnd_4114594 : Nat := 4983230072969 + 3 ^ 40 * 4114594 * 2
def baseEnd_4114594 : Nat := 2112764420105779865752333

theorem tailTrace_4114594 : CollatzResearch.WordTrace tailWord_4114594 prefixEnd_4114594 2112764420105779865752333 := by
  unfold tailWord_4114594
  simp only [CollatzResearch.WordTrace]
  refine ⟨37517893013884032388543709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100047714703690753036116557 37517893013884032388543709)
  ·
    refine ⟨14069209880206512145703891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37517893013884032388543709 14069209880206512145703891)
    ·
      refine ⟨21103814820309768218555837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14069209880206512145703891 21103814820309768218555837)
      ·
        refine ⟨7913930557616163081958439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21103814820309768218555837 7913930557616163081958439)
        ·
          refine ⟨11870895836424244622937659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7913930557616163081958439 11870895836424244622937659)
          ·
            refine ⟨17806343754636366934406489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11870895836424244622937659 17806343754636366934406489)
            ·
              refine ⟨13354757815977275200804867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17806343754636366934406489 13354757815977275200804867)
              ·
                refine ⟨20032136723965912801207301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13354757815977275200804867 20032136723965912801207301)
                ·
                  refine ⟨3756025635743608650226369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20032136723965912801207301 3756025635743608650226369)
                  ·
                    refine ⟨2817019226807706487669777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3756025635743608650226369 2817019226807706487669777)
                    ·
                      refine ⟨2112764420105779865752333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2817019226807706487669777 2112764420105779865752333)
                      ·
                        rfl

theorem cell23_4114594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 2, 1, 4, 2, 2].length) (baseStart_4114594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4114594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4114594 prefixEnd_4114594 := by exact prefixLift 4114594
  have htrace : WordTrace (prefixWord ++ tailWord_4114594) baseStart_4114594 baseEnd_4114594 := by
    simpa [prefixWord, tailWord_4114594, baseEnd_4114594] using wordTrace_append hprefix tailTrace_4114594
  have hstable : (prefixWord ++ tailWord_4114594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4114594).length < 2 ^ (prefixWord ++ tailWord_4114594).sum := by decide
  have hdescent : baseEnd_4114594 < baseStart_4114594 := by decide
  rcases family_descends (prefixWord ++ tailWord_4114594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4114650 : List Nat := [3, 1, 1, 2, 2, 1, 4, 2, 2, 1, 4]
def baseStart_4114650 : Nat := 118140960795 + 4114650 * 2 ^ 59
def prefixEnd_4114650 : Nat := 4983230072969 + 3 ^ 40 * 4114650 * 2
def baseEnd_4114650 : Nat := 2112793175022431646652075

theorem tailTrace_4114650 : CollatzResearch.WordTrace tailWord_4114650 prefixEnd_4114650 2112793175022431646652075 := by
  unfold tailWord_4114650
  simp only [CollatzResearch.WordTrace]
  refine ⟨37518403635833312779553351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100049076362222167412142269 37518403635833312779553351)
  ·
    refine ⟨56277605453749969169330027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37518403635833312779553351 56277605453749969169330027)
    ·
      refine ⟨84416408180624953753995041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56277605453749969169330027 84416408180624953753995041)
      ·
        refine ⟨63312306135468715315496281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84416408180624953753995041 63312306135468715315496281)
        ·
          refine ⟨47484229601601536486622211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63312306135468715315496281 47484229601601536486622211)
          ·
            refine ⟨71226344402402304729933317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47484229601601536486622211 71226344402402304729933317)
            ·
              refine ⟨13354939575450432136862497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 71226344402402304729933317 13354939575450432136862497)
              ·
                refine ⟨10016204681587824102646873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13354939575450432136862497 10016204681587824102646873)
                ·
                  refine ⟨7512153511190868076985155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10016204681587824102646873 7512153511190868076985155)
                  ·
                    refine ⟨11268230266786302115477733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7512153511190868076985155 11268230266786302115477733)
                    ·
                      refine ⟨2112793175022431646652075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11268230266786302115477733 2112793175022431646652075)
                      ·
                        rfl

theorem cell23_4114650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 4, 2, 2, 1, 4].length) (baseStart_4114650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4114650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4114650 prefixEnd_4114650 := by exact prefixLift 4114650
  have htrace : WordTrace (prefixWord ++ tailWord_4114650) baseStart_4114650 baseEnd_4114650 := by
    simpa [prefixWord, tailWord_4114650, baseEnd_4114650] using wordTrace_append hprefix tailTrace_4114650
  have hstable : (prefixWord ++ tailWord_4114650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4114650).length < 2 ^ (prefixWord ++ tailWord_4114650).sum := by decide
  have hdescent : baseEnd_4114650 < baseStart_4114650 := by decide
  rcases family_descends (prefixWord ++ tailWord_4114650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4114660 : List Nat := [2, 3, 1, 1, 1, 2, 1, 5, 3, 4]
def baseStart_4114660 : Nat := 118140960795 + 4114660 * 2 ^ 59
def prefixEnd_4114660 : Nat := 4983230072969 + 3 ^ 40 * 4114660 * 2
def baseEnd_4114660 : Nat := 704266103276325535842343

theorem tailTrace_4114660 : CollatzResearch.WordTrace tailWord_4114660 prefixEnd_4114660 704266103276325535842343 := by
  unfold tailWord_4114660
  simp only [CollatzResearch.WordTrace]
  refine ⟨75036989636648511413038717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100049319515531348550718289 75036989636648511413038717)
  ·
    refine ⟨28138871113743191779889519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75036989636648511413038717 28138871113743191779889519)
    ·
      refine ⟨42208306670614787669834279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28138871113743191779889519 42208306670614787669834279)
      ·
        refine ⟨63312460005922181504751419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42208306670614787669834279 63312460005922181504751419)
        ·
          refine ⟨94968690008883272257127129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63312460005922181504751419 94968690008883272257127129)
          ·
            refine ⟨71226517506662454192845347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94968690008883272257127129 71226517506662454192845347)
            ·
              refine ⟨106839776259993681289268021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71226517506662454192845347 106839776259993681289268021)
              ·
                refine ⟨10016229024374407620868877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 106839776259993681289268021 10016229024374407620868877)
                ·
                  refine ⟨3756085884140402857825829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10016229024374407620868877 3756085884140402857825829)
                  ·
                    refine ⟨704266103276325535842343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3756085884140402857825829 704266103276325535842343)
                    ·
                      rfl

theorem cell23_4114660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 5, 3, 4].length) (baseStart_4114660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4114660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4114660 prefixEnd_4114660 := by exact prefixLift 4114660
  have htrace : WordTrace (prefixWord ++ tailWord_4114660) baseStart_4114660 baseEnd_4114660 := by
    simpa [prefixWord, tailWord_4114660, baseEnd_4114660] using wordTrace_append hprefix tailTrace_4114660
  have hstable : (prefixWord ++ tailWord_4114660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4114660).length < 2 ^ (prefixWord ++ tailWord_4114660).sum := by decide
  have hdescent : baseEnd_4114660 < baseStart_4114660 := by decide
  rcases family_descends (prefixWord ++ tailWord_4114660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4114670 : List Nat := [4, 1, 2, 1, 1, 1, 1, 4, 1, 4, 3]
def baseStart_4114670 : Nat := 118140960795 + 4114670 * 2 ^ 59
def prefixEnd_4114670 : Nat := 4983230072969 + 3 ^ 40 * 4114670 * 2
def baseEnd_4114670 : Nat := 2112803444635521568401983

theorem tailTrace_4114670 : CollatzResearch.WordTrace tailWord_4114670 prefixEnd_4114670 2112803444635521568401983 := by
  unfold tailWord_4114670
  simp only [CollatzResearch.WordTrace]
  refine ⟨18759293000407599316742683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 100049562668840529689294309 18759293000407599316742683)
  ·
    refine ⟨28138939500611398975114025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18759293000407599316742683 28138939500611398975114025)
    ·
      refine ⟨21104204625458549231335519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28138939500611398975114025 21104204625458549231335519)
      ·
        refine ⟨31656306938187823847003279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21104204625458549231335519 31656306938187823847003279)
        ·
          refine ⟨47484460407281735770504919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31656306938187823847003279 47484460407281735770504919)
          ·
            refine ⟨71226690610922603655757379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47484460407281735770504919 71226690610922603655757379)
            ·
              refine ⟨106840035916383905483636069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71226690610922603655757379 106840035916383905483636069)
              ·
                refine ⟨20032506734321982278181763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 106840035916383905483636069 20032506734321982278181763)
                ·
                  refine ⟨30048760101482973417272645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20032506734321982278181763 30048760101482973417272645)
                  ·
                    refine ⟨5634142519028057515738621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30048760101482973417272645 5634142519028057515738621)
                    ·
                      refine ⟨2112803444635521568401983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5634142519028057515738621 2112803444635521568401983)
                      ·
                        rfl

theorem cell23_4114670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 4, 1, 4, 3].length) (baseStart_4114670 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4114670 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4114670 prefixEnd_4114670 := by exact prefixLift 4114670
  have htrace : WordTrace (prefixWord ++ tailWord_4114670) baseStart_4114670 baseEnd_4114670 := by
    simpa [prefixWord, tailWord_4114670, baseEnd_4114670] using wordTrace_append hprefix tailTrace_4114670
  have hstable : (prefixWord ++ tailWord_4114670).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4114670).length < 2 ^ (prefixWord ++ tailWord_4114670).sum := by decide
  have hdescent : baseEnd_4114670 < baseStart_4114670 := by decide
  rcases family_descends (prefixWord ++ tailWord_4114670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4114760 : List Nat := [2, 1, 3, 1, 1, 2, 3, 3, 1, 1, 5]
def baseStart_4114760 : Nat := 118140960795 + 4114760 * 2 ^ 59
def prefixEnd_4114760 : Nat := 4983230072969 + 3 ^ 40 * 4114760 * 2
def baseEnd_4114760 : Nat := 2112849657894426216276569

theorem tailTrace_4114760 : CollatzResearch.WordTrace tailWord_4114760 prefixEnd_4114760 2112849657894426216276569 := by
  unfold tailWord_4114760
  simp only [CollatzResearch.WordTrace]
  refine ⟨75038813286467369952358867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100051751048623159936478489 75038813286467369952358867)
  ·
    refine ⟨112558219929701054928538301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75038813286467369952358867 112558219929701054928538301)
    ·
      refine ⟨42209332473637895598201863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 112558219929701054928538301 42209332473637895598201863)
      ·
        refine ⟨63313998710456843397302795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42209332473637895598201863 63313998710456843397302795)
        ·
          refine ⟨94970998065685265095954193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63313998710456843397302795 94970998065685265095954193)
          ·
            refine ⟨71228248549263948821965645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94970998065685265095954193 71228248549263948821965645)
            ·
              refine ⟨26710593205973980808237117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71228248549263948821965645 26710593205973980808237117)
              ·
                refine ⟨10016472452240242803088919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26710593205973980808237117 10016472452240242803088919)
                ·
                  refine ⟨15024708678360364204633379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10016472452240242803088919 15024708678360364204633379)
                  ·
                    refine ⟨22537063017540546306950069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15024708678360364204633379 22537063017540546306950069)
                    ·
                      refine ⟨2112849657894426216276569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22537063017540546306950069 2112849657894426216276569)
                      ·
                        rfl

theorem cell23_4114760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 3, 3, 1, 1, 5].length) (baseStart_4114760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4114760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4114760 prefixEnd_4114760 := by exact prefixLift 4114760
  have htrace : WordTrace (prefixWord ++ tailWord_4114760) baseStart_4114760 baseEnd_4114760 := by
    simpa [prefixWord, tailWord_4114760, baseEnd_4114760] using wordTrace_append hprefix tailTrace_4114760
  have hstable : (prefixWord ++ tailWord_4114760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4114760).length < 2 ^ (prefixWord ++ tailWord_4114760).sum := by decide
  have hdescent : baseEnd_4114760 < baseStart_4114760 := by decide
  rcases family_descends (prefixWord ++ tailWord_4114760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4114770 : List Nat := [3, 2, 2, 1, 1, 1, 3, 2, 1, 1, 6]
def baseStart_4114770 : Nat := 118140960795 + 4114770 * 2 ^ 59
def prefixEnd_4114770 : Nat := 4983230072969 + 3 ^ 40 * 4114770 * 2
def baseEnd_4114770 : Nat := 2112854792700971177151523

theorem tailTrace_4114770 : CollatzResearch.WordTrace tailWord_4114770 prefixEnd_4114770 2112854792700971177151523 := by
  unfold tailWord_4114770
  simp only [CollatzResearch.WordTrace]
  refine ⟨37519497825724627903145441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100051994201932341075054509 37519497825724627903145441)
  ·
    refine ⟨28139623369293470927359081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37519497825724627903145441 28139623369293470927359081)
    ·
      refine ⟨21104717526970103195519311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28139623369293470927359081 21104717526970103195519311)
      ·
        refine ⟨31657076290455154793278967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21104717526970103195519311 31657076290455154793278967)
        ·
          refine ⟨47485614435682732189918451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31657076290455154793278967 47485614435682732189918451)
          ·
            refine ⟨71228421653524098284877677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47485614435682732189918451 71228421653524098284877677)
            ·
              refine ⟨26710658120071536856829129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71228421653524098284877677 26710658120071536856829129)
              ·
                refine ⟨20032993590053652642621847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26710658120071536856829129 20032993590053652642621847)
                ·
                  refine ⟨30049490385080478963932771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20032993590053652642621847 30049490385080478963932771)
                  ·
                    refine ⟨45074235577620718445899157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30049490385080478963932771 45074235577620718445899157)
                    ·
                      refine ⟨2112854792700971177151523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 45074235577620718445899157 2112854792700971177151523)
                      ·
                        rfl

theorem cell23_4114770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 3, 2, 1, 1, 6].length) (baseStart_4114770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4114770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4114770 prefixEnd_4114770 := by exact prefixLift 4114770
  have htrace : WordTrace (prefixWord ++ tailWord_4114770) baseStart_4114770 baseEnd_4114770 := by
    simpa [prefixWord, tailWord_4114770, baseEnd_4114770] using wordTrace_append hprefix tailTrace_4114770
  have hstable : (prefixWord ++ tailWord_4114770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4114770).length < 2 ^ (prefixWord ++ tailWord_4114770).sum := by decide
  have hdescent : baseEnd_4114770 < baseStart_4114770 := by decide
  rcases family_descends (prefixWord ++ tailWord_4114770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4114784 : List Nat := [2, 1, 1, 3, 5, 1, 1, 3, 2, 4]
def baseStart_4114784 : Nat := 118140960795 + 4114784 * 2 ^ 59
def prefixEnd_4114784 : Nat := 4983230072969 + 3 ^ 40 * 4114784 * 2
def baseEnd_4114784 : Nat := 704287327143378040792153

theorem tailTrace_4114784 : CollatzResearch.WordTrace tailWord_4114784 prefixEnd_4114784 704287327143378040792153 := by
  unfold tailWord_4114784
  simp only [CollatzResearch.WordTrace]
  refine ⟨75039250962423896001795703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100052334616565194669060937 75039250962423896001795703)
  ·
    refine ⟨112558876443635844002693555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75039250962423896001795703 112558876443635844002693555)
    ·
      refine ⟨168838314665453766004040333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112558876443635844002693555 168838314665453766004040333)
      ·
        refine ⟨63314367999545162251515125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 168838314665453766004040333 63314367999545162251515125)
        ·
          refine ⟨5935721999957358961079543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 63314367999545162251515125 5935721999957358961079543)
          ·
            refine ⟨8903582999936038441619315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5935721999957358961079543 8903582999936038441619315)
            ·
              refine ⟨13355374499904057662428973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8903582999936038441619315 13355374499904057662428973)
              ·
                refine ⟨5008265437464021623410865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13355374499904057662428973 5008265437464021623410865)
                ·
                  refine ⟨3756199078098016217558149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5008265437464021623410865 3756199078098016217558149)
                  ·
                    refine ⟨704287327143378040792153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3756199078098016217558149 704287327143378040792153)
                    ·
                      rfl

theorem cell23_4114784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 1, 3, 2, 4].length) (baseStart_4114784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4114784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4114784 prefixEnd_4114784 := by exact prefixLift 4114784
  have htrace : WordTrace (prefixWord ++ tailWord_4114784) baseStart_4114784 baseEnd_4114784 := by
    simpa [prefixWord, tailWord_4114784, baseEnd_4114784] using wordTrace_append hprefix tailTrace_4114784
  have hstable : (prefixWord ++ tailWord_4114784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4114784).length < 2 ^ (prefixWord ++ tailWord_4114784).sum := by decide
  have hdescent : baseEnd_4114784 < baseStart_4114784 := by decide
  rcases family_descends (prefixWord ++ tailWord_4114784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4114794 : List Nat := [3, 1, 3, 3, 1, 2, 1, 1, 3, 2, 3]
def baseStart_4114794 : Nat := 118140960795 + 4114794 * 2 ^ 59
def prefixEnd_4114794 : Nat := 4983230072969 + 3 ^ 40 * 4114794 * 2
def baseEnd_4114794 : Nat := 2112867116236679083251413

theorem tailTrace_4114794 : CollatzResearch.WordTrace tailWord_4114794 prefixEnd_4114794 2112867116236679083251413 := by
  unfold tailWord_4114794
  simp only [CollatzResearch.WordTrace]
  refine ⟨37519716663702890927863859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100052577769874375807636957 37519716663702890927863859)
  ·
    refine ⟨56279574995554336391795789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37519716663702890927863859 56279574995554336391795789)
    ·
      refine ⟨21104840623332876146923421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56279574995554336391795789 21104840623332876146923421)
      ·
        refine ⟨7914315233749828555096283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21104840623332876146923421 7914315233749828555096283)
        ·
          refine ⟨11871472850624742832644425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7914315233749828555096283 11871472850624742832644425)
          ·
            refine ⟨8903604637968557124483319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11871472850624742832644425 8903604637968557124483319)
            ·
              refine ⟨13355406956952835686724979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8903604637968557124483319 13355406956952835686724979)
              ·
                refine ⟨20033110435429253530087469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13355406956952835686724979 20033110435429253530087469)
                ·
                  refine ⟨7512416413285970073782801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20033110435429253530087469 7512416413285970073782801)
                  ·
                    refine ⟨5634312309964477555337101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7512416413285970073782801 5634312309964477555337101)
                    ·
                      refine ⟨2112867116236679083251413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5634312309964477555337101 2112867116236679083251413)
                      ·
                        rfl

theorem cell23_4114794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 1, 1, 3, 2, 3].length) (baseStart_4114794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4114794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4114794 prefixEnd_4114794 := by exact prefixLift 4114794
  have htrace : WordTrace (prefixWord ++ tailWord_4114794) baseStart_4114794 baseEnd_4114794 := by
    simpa [prefixWord, tailWord_4114794, baseEnd_4114794] using wordTrace_append hprefix tailTrace_4114794
  have hstable : (prefixWord ++ tailWord_4114794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4114794).length < 2 ^ (prefixWord ++ tailWord_4114794).sum := by decide
  have hdescent : baseEnd_4114794 < baseStart_4114794 := by decide
  rcases family_descends (prefixWord ++ tailWord_4114794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4114807 : List Nat := [1, 1, 3, 1, 1, 2, 2, 4, 4, 1, 3]
def baseStart_4114807 : Nat := 118140960795 + 4114807 * 2 ^ 59
def prefixEnd_4114807 : Nat := 4983230072969 + 3 ^ 40 * 4114807 * 2
def baseEnd_4114807 : Nat := 2112873791485187532388853

theorem tailTrace_4114807 : CollatzResearch.WordTrace tailWord_4114807 prefixEnd_4114807 2112873791485187532388853 := by
  unfold tailWord_4114807
  simp only [CollatzResearch.WordTrace]
  refine ⟨150079340803764466931678675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100052893869176311287785783 150079340803764466931678675)
  ·
    refine ⟨225119011205646700397518013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150079340803764466931678675 225119011205646700397518013)
    ·
      refine ⟨84419629202117512649069255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 225119011205646700397518013 84419629202117512649069255)
      ·
        refine ⟨126629443803176268973603883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84419629202117512649069255 126629443803176268973603883)
        ·
          refine ⟨189944165704764403460405825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126629443803176268973603883 189944165704764403460405825)
          ·
            refine ⟨142458124278573302595304369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 189944165704764403460405825 142458124278573302595304369)
            ·
              refine ⟨106843593208929976946478277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 142458124278573302595304369 106843593208929976946478277)
              ·
                refine ⟨20033173726674370677464677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 106843593208929976946478277 20033173726674370677464677)
                ·
                  refine ⟨3756220073751444502024627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20033173726674370677464677 3756220073751444502024627)
                  ·
                    refine ⟨5634330110627166753036941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3756220073751444502024627 5634330110627166753036941)
                    ·
                      refine ⟨2112873791485187532388853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5634330110627166753036941 2112873791485187532388853)
                      ·
                        rfl

theorem cell23_4114807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 4, 4, 1, 3].length) (baseStart_4114807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4114807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4114807 prefixEnd_4114807 := by exact prefixLift 4114807
  have htrace : WordTrace (prefixWord ++ tailWord_4114807) baseStart_4114807 baseEnd_4114807 := by
    simpa [prefixWord, tailWord_4114807, baseEnd_4114807] using wordTrace_append hprefix tailTrace_4114807
  have hstable : (prefixWord ++ tailWord_4114807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4114807).length < 2 ^ (prefixWord ++ tailWord_4114807).sum := by decide
  have hdescent : baseEnd_4114807 < baseStart_4114807 := by decide
  rcases family_descends (prefixWord ++ tailWord_4114807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4114818 : List Nat := [3, 4, 2, 1, 2, 1, 2, 2, 2, 4]
def baseStart_4114818 : Nat := 118140960795 + 4114818 * 2 ^ 59
def prefixEnd_4114818 : Nat := 4983230072969 + 3 ^ 40 * 4114818 * 2
def baseEnd_4114818 : Nat := 704293146590795663117101

theorem tailTrace_4114818 : CollatzResearch.WordTrace tailWord_4114818 prefixEnd_4114818 704293146590795663117101 := by
  unfold tailWord_4114818
  simp only [CollatzResearch.WordTrace]
  refine ⟨37519935501681153952582277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100053161337816410540219405 37519935501681153952582277)
  ·
    refine ⟨7034987906565216366109177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37519935501681153952582277 7034987906565216366109177)
    ·
      refine ⟨5276240929923912274581883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7034987906565216366109177 5276240929923912274581883)
      ·
        refine ⟨7914361394885868411872825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5276240929923912274581883 7914361394885868411872825)
        ·
          refine ⟨5935771046164401308904619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7914361394885868411872825 5935771046164401308904619)
          ·
            refine ⟨8903656569246601963356929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5935771046164401308904619 8903656569246601963356929)
            ·
              refine ⟨6677742426934951472517697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8903656569246601963356929 6677742426934951472517697)
              ·
                refine ⟨5008306820201213604388273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6677742426934951472517697 5008306820201213604388273)
                ·
                  refine ⟨3756230115150910203291205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5008306820201213604388273 3756230115150910203291205)
                  ·
                    refine ⟨704293146590795663117101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3756230115150910203291205 704293146590795663117101)
                    ·
                      rfl

theorem cell23_4114818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 2, 2, 2, 4].length) (baseStart_4114818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4114818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4114818 prefixEnd_4114818 := by exact prefixLift 4114818
  have htrace : WordTrace (prefixWord ++ tailWord_4114818) baseStart_4114818 baseEnd_4114818 := by
    simpa [prefixWord, tailWord_4114818, baseEnd_4114818] using wordTrace_append hprefix tailTrace_4114818
  have hstable : (prefixWord ++ tailWord_4114818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4114818).length < 2 ^ (prefixWord ++ tailWord_4114818).sum := by decide
  have hdescent : baseEnd_4114818 < baseStart_4114818 := by decide
  rcases family_descends (prefixWord ++ tailWord_4114818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4114825 : List Nat := [1, 2, 1, 1, 6, 3, 2, 2, 1, 2, 2]
def baseStart_4114825 : Nat := 118140960795 + 4114825 * 2 ^ 59
def prefixEnd_4114825 : Nat := 4983230072969 + 3 ^ 40 * 4114825 * 2
def baseEnd_4114825 : Nat := 2112883034136968461963771

theorem tailTrace_4114825 : CollatzResearch.WordTrace tailWord_4114825 prefixEnd_4114825 2112883034136968461963771 := by
  unfold tailWord_4114825
  simp only [CollatzResearch.WordTrace]
  refine ⟨150079997317699256005833929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100053331545132837337222619 150079997317699256005833929)
  ·
    refine ⟨112559997988274442004375447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150079997317699256005833929 112559997988274442004375447)
    ·
      refine ⟨168839996982411663006563171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112559997988274442004375447 168839996982411663006563171)
      ·
        refine ⟨253259995473617494509844757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168839996982411663006563171 253259995473617494509844757)
        ·
          refine ⟨11871562287825820055148973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 253259995473617494509844757 11871562287825820055148973)
          ·
            refine ⟨4451835857934682520680865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11871562287825820055148973 4451835857934682520680865)
            ·
              refine ⟨3338876893451011890510649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4451835857934682520680865 3338876893451011890510649)
              ·
                refine ⟨2504157670088258917882987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3338876893451011890510649 2504157670088258917882987)
                ·
                  refine ⟨3756236505132388376824481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2504157670088258917882987 3756236505132388376824481)
                  ·
                    refine ⟨2817177378849291282618361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3756236505132388376824481 2817177378849291282618361)
                    ·
                      refine ⟨2112883034136968461963771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2817177378849291282618361 2112883034136968461963771)
                      ·
                        rfl

theorem cell23_4114825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 3, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 3, 2, 2, 1, 2, 2].length) (baseStart_4114825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4114825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4114825 prefixEnd_4114825 := by exact prefixLift 4114825
  have htrace : WordTrace (prefixWord ++ tailWord_4114825) baseStart_4114825 baseEnd_4114825 := by
    simpa [prefixWord, tailWord_4114825, baseEnd_4114825] using wordTrace_append hprefix tailTrace_4114825
  have hstable : (prefixWord ++ tailWord_4114825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4114825).length < 2 ^ (prefixWord ++ tailWord_4114825).sum := by decide
  have hdescent : baseEnd_4114825 < baseStart_4114825 := by decide
  rcases family_descends (prefixWord ++ tailWord_4114825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4114860 : List Nat := [2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 4]
def baseStart_4114860 : Nat := 118140960795 + 4114860 * 2 ^ 59
def prefixEnd_4114860 : Nat := 4983230072969 + 3 ^ 40 * 4114860 * 2
def baseEnd_4114860 : Nat := 2112901005959875825026109

theorem tailTrace_4114860 : CollatzResearch.WordTrace tailWord_4114860 prefixEnd_4114860 2112901005959875825026109 := by
  unfold tailWord_4114860
  simp only [CollatzResearch.WordTrace]
  refine ⟨75040636936286228491679017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100054182581714971322238689 75040636936286228491679017)
  ·
    refine ⟨56280477702214671368759263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75040636936286228491679017 56280477702214671368759263)
    ·
      refine ⟨84420716553322007053138895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56280477702214671368759263 84420716553322007053138895)
      ·
        refine ⟨126631074829983010579708343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84420716553322007053138895 126631074829983010579708343)
        ·
          refine ⟨189946612244974515869562515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126631074829983010579708343 189946612244974515869562515)
          ·
            refine ⟨284919918367461773804343773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 189946612244974515869562515 284919918367461773804343773)
            ·
              refine ⟨106844969387798165176628915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 284919918367461773804343773 106844969387798165176628915)
              ·
                refine ⟨160267454081697247764943373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 106844969387798165176628915 160267454081697247764943373)
                ·
                  refine ⟨60100295280636467911853765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 160267454081697247764943373 60100295280636467911853765)
                  ·
                    refine ⟨11268805365119337733472581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 60100295280636467911853765 11268805365119337733472581)
                    ·
                      refine ⟨2112901005959875825026109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11268805365119337733472581 2112901005959875825026109)
                      ·
                        rfl

theorem cell23_4114860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 4].length) (baseStart_4114860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4114860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4114860 prefixEnd_4114860 := by exact prefixLift 4114860
  have htrace : WordTrace (prefixWord ++ tailWord_4114860) baseStart_4114860 baseEnd_4114860 := by
    simpa [prefixWord, tailWord_4114860, baseEnd_4114860] using wordTrace_append hprefix tailTrace_4114860
  have hstable : (prefixWord ++ tailWord_4114860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4114860).length < 2 ^ (prefixWord ++ tailWord_4114860).sum := by decide
  have hdescent : baseEnd_4114860 < baseStart_4114860 := by decide
  rcases family_descends (prefixWord ++ tailWord_4114860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4114877 : List Nat := [1, 4, 1, 2, 2, 2, 1, 2, 2, 2, 4]
def baseStart_4114877 : Nat := 118140960795 + 4114877 * 2 ^ 59
def prefixEnd_4114877 : Nat := 4983230072969 + 3 ^ 40 * 4114877 * 2
def baseEnd_4114877 : Nat := 2112909735131002258513531

theorem tailTrace_4114877 : CollatzResearch.WordTrace tailWord_4114877 prefixEnd_4114877 2112909735131002258513531 := by
  unfold tailWord_4114877
  simp only [CollatzResearch.WordTrace]
  refine ⟨150081893913510868886726885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100054595942340579257817923 150081893913510868886726885)
  ·
    refine ⟨28140355108783287916261291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 150081893913510868886726885 28140355108783287916261291)
    ·
      refine ⟨42210532663174931874391937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28140355108783287916261291 42210532663174931874391937)
      ·
        refine ⟨31657899497381198905793953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42210532663174931874391937 31657899497381198905793953)
        ·
          refine ⟨23743424623035899179345465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31657899497381198905793953 23743424623035899179345465)
          ·
            refine ⟨17807568467276924384509099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23743424623035899179345465 17807568467276924384509099)
            ·
              refine ⟨26711352700915386576763649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17807568467276924384509099 26711352700915386576763649)
              ·
                refine ⟨20033514525686539932572737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26711352700915386576763649 20033514525686539932572737)
                ·
                  refine ⟨15025135894264904949429553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20033514525686539932572737 15025135894264904949429553)
                  ·
                    refine ⟨11268851920698678712072165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15025135894264904949429553 11268851920698678712072165)
                    ·
                      refine ⟨2112909735131002258513531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11268851920698678712072165 2112909735131002258513531)
                      ·
                        rfl

theorem cell23_4114877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 1, 2, 2, 2, 4].length) (baseStart_4114877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4114877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4114877 prefixEnd_4114877 := by exact prefixLift 4114877
  have htrace : WordTrace (prefixWord ++ tailWord_4114877) baseStart_4114877 baseEnd_4114877 := by
    simpa [prefixWord, tailWord_4114877, baseEnd_4114877] using wordTrace_append hprefix tailTrace_4114877
  have hstable : (prefixWord ++ tailWord_4114877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4114877).length < 2 ^ (prefixWord ++ tailWord_4114877).sum := by decide
  have hdescent : baseEnd_4114877 < baseStart_4114877 := by decide
  rcases family_descends (prefixWord ++ tailWord_4114877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4114887 : List Nat := [1, 1, 4, 1, 1, 5, 2, 1, 7]
def baseStart_4114887 : Nat := 118140960795 + 4114887 * 2 ^ 59
def prefixEnd_4114887 : Nat := 4983230072969 + 3 ^ 40 * 4114887 * 2
def baseEnd_4114887 : Nat := 234768318881949691043165

theorem tailTrace_4114887 : CollatzResearch.WordTrace tailWord_4114887 prefixEnd_4114887 234768318881949691043165 := by
  unfold tailWord_4114887
  simp only [CollatzResearch.WordTrace]
  refine ⟨150082258643474640594590915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100054839095649760396393943 150082258643474640594590915)
  ·
    refine ⟨225123387965211960891886373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150082258643474640594590915 225123387965211960891886373)
    ·
      refine ⟨42210635243477242667228695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 225123387965211960891886373 42210635243477242667228695)
      ·
        refine ⟨63315952865215864000843043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42210635243477242667228695 63315952865215864000843043)
        ·
          refine ⟨94973929297823796001264565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63315952865215864000843043 94973929297823796001264565)
          ·
            refine ⟨8903805871670980875118553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 94973929297823796001264565 8903805871670980875118553)
            ·
              refine ⟨6677854403753235656338915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8903805871670980875118553 6677854403753235656338915)
              ·
                refine ⟨10016781605629853484508373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6677854403753235656338915 10016781605629853484508373)
                ·
                  refine ⟨234768318881949691043165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10016781605629853484508373 234768318881949691043165)
                  ·
                    rfl

theorem cell23_4114887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 2, 1, 7].length) (baseStart_4114887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4114887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4114887 prefixEnd_4114887 := by exact prefixLift 4114887
  have htrace : WordTrace (prefixWord ++ tailWord_4114887) baseStart_4114887 baseEnd_4114887 := by
    simpa [prefixWord, tailWord_4114887, baseEnd_4114887] using wordTrace_append hprefix tailTrace_4114887
  have hstable : (prefixWord ++ tailWord_4114887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4114887).length < 2 ^ (prefixWord ++ tailWord_4114887).sum := by decide
  have hdescent : baseEnd_4114887 < baseStart_4114887 := by decide
  rcases family_descends (prefixWord ++ tailWord_4114887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4114934 : List Nat := [5, 1, 1, 1, 2, 1, 3, 2, 2, 5]
def baseStart_4114934 : Nat := 118140960795 + 4114934 * 2 ^ 59
def prefixEnd_4114934 : Nat := 4983230072969 + 3 ^ 40 * 4114934 * 2
def baseEnd_4114934 : Nat := 704313001176102845166923

theorem tailTrace_4114934 : CollatzResearch.WordTrace tailWord_4114934 prefixEnd_4114934 704313001176102845166923 := by
  unfold tailWord_4114934
  simp only [CollatzResearch.WordTrace]
  refine ⟨9380248304644022976346991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 100055981916202911747701237 9380248304644022976346991)
  ·
    refine ⟨14070372456966034464520487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9380248304644022976346991 14070372456966034464520487)
    ·
      refine ⟨21105558685449051696780731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14070372456966034464520487 21105558685449051696780731)
      ·
        refine ⟨31658338028173577545171097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21105558685449051696780731 31658338028173577545171097)
        ·
          refine ⟨23743753521130183158878323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31658338028173577545171097 23743753521130183158878323)
          ·
            refine ⟨35615630281695274738317485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23743753521130183158878323 35615630281695274738317485)
            ·
              refine ⟨13355861355635728026869057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35615630281695274738317485 13355861355635728026869057)
              ·
                refine ⟨10016896016726796020151793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13355861355635728026869057 10016896016726796020151793)
                ·
                  refine ⟨7512672012545097015113845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10016896016726796020151793 7512672012545097015113845)
                  ·
                    refine ⟨704313001176102845166923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7512672012545097015113845 704313001176102845166923)
                    ·
                      rfl

theorem cell23_4114934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 3, 2, 2, 5].length) (baseStart_4114934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4114934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4114934 prefixEnd_4114934 := by exact prefixLift 4114934
  have htrace : WordTrace (prefixWord ++ tailWord_4114934) baseStart_4114934 baseEnd_4114934 := by
    simpa [prefixWord, tailWord_4114934, baseEnd_4114934] using wordTrace_append hprefix tailTrace_4114934
  have hstable : (prefixWord ++ tailWord_4114934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4114934).length < 2 ^ (prefixWord ++ tailWord_4114934).sum := by decide
  have hdescent : baseEnd_4114934 < baseStart_4114934 := by decide
  rcases family_descends (prefixWord ++ tailWord_4114934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4114937 : List Nat := [1, 2, 1, 3, 1, 2, 3, 1, 4, 1, 4]
def baseStart_4114937 : Nat := 118140960795 + 4114937 * 2 ^ 59
def prefixEnd_4114937 : Nat := 4983230072969 + 3 ^ 40 * 4114937 * 2
def baseEnd_4114937 : Nat := 2112940543970272023763255

theorem tailTrace_4114937 : CollatzResearch.WordTrace tailWord_4114937 prefixEnd_4114937 2112940543970272023763255 := by
  unfold tailWord_4114937
  simp only [CollatzResearch.WordTrace]
  refine ⟨150084082293293499133911065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100056054862195666089274043 150084082293293499133911065)
  ·
    refine ⟨112563061719970124350433299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150084082293293499133911065 112563061719970124350433299)
    ·
      refine ⟨168844592579955186525649949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112563061719970124350433299 168844592579955186525649949)
      ·
        refine ⟨63316722217483194947118731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 168844592579955186525649949 63316722217483194947118731)
        ·
          refine ⟨94975083326224792420678097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63316722217483194947118731 94975083326224792420678097)
          ·
            refine ⟨71231312494668594315508573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94975083326224792420678097 71231312494668594315508573)
            ·
              refine ⟨26711742185500722868315715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71231312494668594315508573 26711742185500722868315715)
              ·
                refine ⟨40067613278251084302473573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26711742185500722868315715 40067613278251084302473573)
                ·
                  refine ⟨7512677489672078306713795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40067613278251084302473573 7512677489672078306713795)
                  ·
                    refine ⟨11269016234508117460070693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7512677489672078306713795 11269016234508117460070693)
                    ·
                      refine ⟨2112940543970272023763255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11269016234508117460070693 2112940543970272023763255)
                      ·
                        rfl

theorem cell23_4114937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 3, 1, 4, 1, 4].length) (baseStart_4114937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4114937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4114937 prefixEnd_4114937 := by exact prefixLift 4114937
  have htrace : WordTrace (prefixWord ++ tailWord_4114937) baseStart_4114937 baseEnd_4114937 := by
    simpa [prefixWord, tailWord_4114937, baseEnd_4114937] using wordTrace_append hprefix tailTrace_4114937
  have hstable : (prefixWord ++ tailWord_4114937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4114937).length < 2 ^ (prefixWord ++ tailWord_4114937).sum := by decide
  have hdescent : baseEnd_4114937 < baseStart_4114937 := by decide
  rcases family_descends (prefixWord ++ tailWord_4114937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4114954 : List Nat := [3, 1, 2, 2, 2, 1, 2, 1, 1, 6, 2]
def baseStart_4114954 : Nat := 118140960795 + 4114954 * 2 ^ 59
def prefixEnd_4114954 : Nat := 4983230072969 + 3 ^ 40 * 4114954 * 2
def baseEnd_4114954 : Nat := 2112949273141398457250677

theorem tailTrace_4114954 : CollatzResearch.WordTrace tailWord_4114954 prefixEnd_4114954 2112949273141398457250677 := by
  unfold tailWord_4114954
  simp only [CollatzResearch.WordTrace]
  refine ⟨37521175583557977759319979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100056468222821274024853277 37521175583557977759319979)
  ·
    refine ⟨56281763375336966638979969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37521175583557977759319979 56281763375336966638979969)
    ·
      refine ⟨42211322531502724979234977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56281763375336966638979969 42211322531502724979234977)
      ·
        refine ⟨31658491898627043734426233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42211322531502724979234977 31658491898627043734426233)
        ·
          refine ⟨23743868923970282800819675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31658491898627043734426233 23743868923970282800819675)
          ·
            refine ⟨35615803385955424201229513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23743868923970282800819675 35615803385955424201229513)
            ·
              refine ⟨26711852539466568150922135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35615803385955424201229513 26711852539466568150922135)
              ·
                refine ⟨40067778809199852226383203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26711852539466568150922135 40067778809199852226383203)
                ·
                  refine ⟨60101668213799778339574805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40067778809199852226383203 60101668213799778339574805)
                  ·
                    refine ⟨2817265697521864609667569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 60101668213799778339574805 2817265697521864609667569)
                    ·
                      refine ⟨2112949273141398457250677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2817265697521864609667569 2112949273141398457250677)
                      ·
                        rfl

theorem cell23_4114954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 2, 1, 1, 6, 2].length) (baseStart_4114954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4114954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4114954 prefixEnd_4114954 := by exact prefixLift 4114954
  have htrace : WordTrace (prefixWord ++ tailWord_4114954) baseStart_4114954 baseEnd_4114954 := by
    simpa [prefixWord, tailWord_4114954, baseEnd_4114954] using wordTrace_append hprefix tailTrace_4114954
  have hstable : (prefixWord ++ tailWord_4114954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4114954).length < 2 ^ (prefixWord ++ tailWord_4114954).sum := by decide
  have hdescent : baseEnd_4114954 < baseStart_4114954 := by decide
  rcases family_descends (prefixWord ++ tailWord_4114954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4114989 : List Nat := [1, 5, 4, 1, 2, 1, 2, 2, 5]
def baseStart_4114989 : Nat := 118140960795 + 4114989 * 2 ^ 59
def prefixEnd_4114989 : Nat := 4983230072969 + 3 ^ 40 * 4114989 * 2
def baseEnd_4114989 : Nat := 234774138329367313368113

theorem tailTrace_4114989 : CollatzResearch.WordTrace tailWord_4114989 prefixEnd_4114989 234774138329367313368113 := by
  unfold tailWord_4114989
  simp only [CollatzResearch.WordTrace]
  refine ⟨150085978889105112014804021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100057319259403408009869347 150085978889105112014804021)
  ·
    refine ⟨14070560520853604251387877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 150085978889105112014804021 14070560520853604251387877)
    ·
      refine ⟨2638230097660050797135227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14070560520853604251387877 2638230097660050797135227)
      ·
        refine ⟨3957345146490076195702841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2638230097660050797135227 3957345146490076195702841)
        ·
          refine ⟨2968008859867557146777131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3957345146490076195702841 2968008859867557146777131)
          ·
            refine ⟨4452013289801335720165697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2968008859867557146777131 4452013289801335720165697)
            ·
              refine ⟨3339009967351001790124273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4452013289801335720165697 3339009967351001790124273)
              ·
                refine ⟨2504257475513251342593205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3339009967351001790124273 2504257475513251342593205)
                ·
                  refine ⟨234774138329367313368113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2504257475513251342593205 234774138329367313368113)
                  ·
                    rfl

theorem cell23_4114989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 2, 1, 2, 2, 5].length) (baseStart_4114989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4114989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4114989 prefixEnd_4114989 := by exact prefixLift 4114989
  have htrace : WordTrace (prefixWord ++ tailWord_4114989) baseStart_4114989 baseEnd_4114989 := by
    simpa [prefixWord, tailWord_4114989, baseEnd_4114989] using wordTrace_append hprefix tailTrace_4114989
  have hstable : (prefixWord ++ tailWord_4114989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4114989).length < 2 ^ (prefixWord ++ tailWord_4114989).sum := by decide
  have hdescent : baseEnd_4114989 < baseStart_4114989 := by decide
  rcases family_descends (prefixWord ++ tailWord_4114989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4114997 : List Nat := [1, 3, 3, 1, 1, 2, 2, 1, 1, 2, 6]
def baseStart_4114997 : Nat := 118140960795 + 4114997 * 2 ^ 59
def prefixEnd_4114997 : Nat := 4983230072969 + 3 ^ 40 * 4114997 * 2
def baseEnd_4114997 : Nat := 2112971352809541789012979

theorem tailTrace_4114997 : CollatzResearch.WordTrace tailWord_4114997 prefixEnd_4114997 2112971352809541789012979 := by
  unfold tailWord_4114997
  simp only [CollatzResearch.WordTrace]
  refine ⟨150086270673076129381095245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100057513782050752920730163 150086270673076129381095245)
  ·
    refine ⟨56282351502403548517910717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 150086270673076129381095245 56282351502403548517910717)
    ·
      refine ⟨21105881813401330694216519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56282351502403548517910717 21105881813401330694216519)
      ·
        refine ⟨31658822720101996041324779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21105881813401330694216519 31658822720101996041324779)
        ·
          refine ⟨47488234080152994061987169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31658822720101996041324779 47488234080152994061987169)
          ·
            refine ⟨35616175560114745546490377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47488234080152994061987169 35616175560114745546490377)
            ·
              refine ⟨26712131670086059159867783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35616175560114745546490377 26712131670086059159867783)
              ·
                refine ⟨40068197505129088739801675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26712131670086059159867783 40068197505129088739801675)
                ·
                  refine ⟨60102296257693633109702513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40068197505129088739801675 60102296257693633109702513)
                  ·
                    refine ⟨45076722193270224832276885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 60102296257693633109702513 45076722193270224832276885)
                    ·
                      refine ⟨2112971352809541789012979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 45076722193270224832276885 2112971352809541789012979)
                      ·
                        rfl

theorem cell23_4114997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 2, 1, 1, 2, 6].length) (baseStart_4114997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4114997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4114997 prefixEnd_4114997 := by exact prefixLift 4114997
  have htrace : WordTrace (prefixWord ++ tailWord_4114997) baseStart_4114997 baseEnd_4114997 := by
    simpa [prefixWord, tailWord_4114997, baseEnd_4114997] using wordTrace_append hprefix tailTrace_4114997
  have hstable : (prefixWord ++ tailWord_4114997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4114997).length < 2 ^ (prefixWord ++ tailWord_4114997).sum := by decide
  have hdescent : baseEnd_4114997 < baseStart_4114997 := by decide
  rcases family_descends (prefixWord ++ tailWord_4114997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4115007 : List Nat := [1, 1, 2, 2, 3, 2, 1, 1, 5, 5]
def baseStart_4115007 : Nat := 118140960795 + 4115007 * 2 ^ 59
def prefixEnd_4115007 : Nat := 4983230072969 + 3 ^ 40 * 4115007 * 2
def baseEnd_4115007 : Nat := 704325495872028916629311

theorem tailTrace_4115007 : CollatzResearch.WordTrace tailWord_4115007 prefixEnd_4115007 704325495872028916629311 := by
  unfold tailWord_4115007
  simp only [CollatzResearch.WordTrace]
  refine ⟨150086635403039901088959275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100057756935359934059306183 150086635403039901088959275)
  ·
    refine ⟨225129953104559851633438913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150086635403039901088959275 225129953104559851633438913)
    ·
      refine ⟨168847464828419888725079185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 225129953104559851633438913 168847464828419888725079185)
      ·
        refine ⟨126635598621314916543809389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 168847464828419888725079185 126635598621314916543809389)
        ·
          refine ⟨47488349482993093703928521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 126635598621314916543809389 47488349482993093703928521)
          ·
            refine ⟨35616262112244820277946391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47488349482993093703928521 35616262112244820277946391)
            ·
              refine ⟨53424393168367230416919587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35616262112244820277946391 53424393168367230416919587)
              ·
                refine ⟨80136589752550845625379381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53424393168367230416919587 80136589752550845625379381)
                ·
                  refine ⟨7512805289301641777379317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 80136589752550845625379381 7512805289301641777379317)
                  ·
                    refine ⟨704325495872028916629311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7512805289301641777379317 704325495872028916629311)
                    ·
                      rfl

theorem cell23_4115007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 1, 5, 5].length) (baseStart_4115007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4115007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4115007 prefixEnd_4115007 := by exact prefixLift 4115007
  have htrace : WordTrace (prefixWord ++ tailWord_4115007) baseStart_4115007 baseEnd_4115007 := by
    simpa [prefixWord, tailWord_4115007, baseEnd_4115007] using wordTrace_append hprefix tailTrace_4115007
  have hstable : (prefixWord ++ tailWord_4115007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4115007).length < 2 ^ (prefixWord ++ tailWord_4115007).sum := by decide
  have hdescent : baseEnd_4115007 < baseStart_4115007 := by decide
  rcases family_descends (prefixWord ++ tailWord_4115007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4115041 : List Nat := [1, 2, 3, 1, 1, 4, 4, 1, 1, 5]
def baseStart_4115041 : Nat := 118140960795 + 4115041 * 2 ^ 59
def prefixEnd_4115041 : Nat := 4983230072969 + 3 ^ 40 * 4115041 * 2
def baseEnd_4115041 : Nat := 704331315319446538954259

theorem tailTrace_4115041 : CollatzResearch.WordTrace tailWord_4115041 prefixEnd_4115041 704331315319446538954259 := by
  unfold tailWord_4115041
  simp only [CollatzResearch.WordTrace]
  refine ⟨150087875484916724895696977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100058583656611149930464651 150087875484916724895696977)
  ·
    refine ⟨112565906613687543671772733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150087875484916724895696977 112565906613687543671772733)
    ·
      refine ⟨42212214980132828876914775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 112565906613687543671772733 42212214980132828876914775)
      ·
        refine ⟨63318322470199243315372163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42212214980132828876914775 63318322470199243315372163)
        ·
          refine ⟨94977483705298864973058245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63318322470199243315372163 94977483705298864973058245)
          ·
            refine ⟨17808278194743537182448421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 94977483705298864973058245 17808278194743537182448421)
            ·
              refine ⟨3339052161514413221709079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17808278194743537182448421 3339052161514413221709079)
              ·
                refine ⟨5008578242271619832563619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3339052161514413221709079 5008578242271619832563619)
                ·
                  refine ⟨7512867363407429748845429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5008578242271619832563619 7512867363407429748845429)
                  ·
                    refine ⟨704331315319446538954259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7512867363407429748845429 704331315319446538954259)
                    ·
                      rfl

theorem cell23_4115041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 4, 1, 1, 5].length) (baseStart_4115041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4115041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4115041 prefixEnd_4115041 := by exact prefixLift 4115041
  have htrace : WordTrace (prefixWord ++ tailWord_4115041) baseStart_4115041 baseEnd_4115041 := by
    simpa [prefixWord, tailWord_4115041, baseEnd_4115041] using wordTrace_append hprefix tailTrace_4115041
  have hstable : (prefixWord ++ tailWord_4115041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4115041).length < 2 ^ (prefixWord ++ tailWord_4115041).sum := by decide
  have hdescent : baseEnd_4115041 < baseStart_4115041 := by decide
  rcases family_descends (prefixWord ++ tailWord_4115041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4115057 : List Nat := [1, 2, 2, 2, 1, 1, 1, 1, 2, 6, 4]
def baseStart_4115057 : Nat := 118140960795 + 4115057 * 2 ^ 59
def prefixEnd_4115057 : Nat := 4983230072969 + 3 ^ 40 * 4115057 * 2
def baseEnd_4115057 : Nat := 2113002161648811554262703

theorem tailTrace_4115057 : CollatzResearch.WordTrace tailWord_4115057 prefixEnd_4115057 2113002161648811554262703 := by
  unfold tailWord_4115057
  simp only [CollatzResearch.WordTrace]
  refine ⟨150088459052858759628279425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100058972701905839752186283 150088459052858759628279425)
  ·
    refine ⟨112566344289644069721209569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150088459052858759628279425 112566344289644069721209569)
    ·
      refine ⟨84424758217233052290907177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112566344289644069721209569 84424758217233052290907177)
      ·
        refine ⟨63318568662924789218180383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84424758217233052290907177 63318568662924789218180383)
        ·
          refine ⟨94977852994387183827270575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63318568662924789218180383 94977852994387183827270575)
          ·
            refine ⟨142466779491580775740905863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94977852994387183827270575 142466779491580775740905863)
            ·
              refine ⟨213700169237371163611358795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 142466779491580775740905863 213700169237371163611358795)
              ·
                refine ⟨320550253856056745417038193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 213700169237371163611358795 320550253856056745417038193)
                ·
                  refine ⟨240412690392042559062778645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 320550253856056745417038193 240412690392042559062778645)
                  ·
                    refine ⟨11269344862126994956067749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 240412690392042559062778645 11269344862126994956067749)
                    ·
                      refine ⟨2113002161648811554262703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11269344862126994956067749 2113002161648811554262703)
                      ·
                        rfl

theorem cell23_4115057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 1, 2, 6, 4].length) (baseStart_4115057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4115057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4115057 prefixEnd_4115057 := by exact prefixLift 4115057
  have htrace : WordTrace (prefixWord ++ tailWord_4115057) baseStart_4115057 baseEnd_4115057 := by
    simpa [prefixWord, tailWord_4115057, baseEnd_4115057] using wordTrace_append hprefix tailTrace_4115057
  have hstable : (prefixWord ++ tailWord_4115057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4115057).length < 2 ^ (prefixWord ++ tailWord_4115057).sum := by decide
  have hdescent : baseEnd_4115057 < baseStart_4115057 := by decide
  rcases family_descends (prefixWord ++ tailWord_4115057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4115098 : List Nat := [3, 1, 1, 6, 1, 1, 2, 1, 1, 1, 5]
def baseStart_4115098 : Nat := 118140960795 + 4115098 * 2 ^ 59
def prefixEnd_4115098 : Nat := 4983230072969 + 3 ^ 40 * 4115098 * 2
def baseEnd_4115098 : Nat := 2113023214355645893850015

theorem tailTrace_4115098 : CollatzResearch.WordTrace tailWord_4115098 prefixEnd_4115098 2113023214355645893850015 := by
  unfold tailWord_4115098
  simp only [CollatzResearch.WordTrace]
  refine ⟨37522488611427555907630487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100059969630473482420347965 37522488611427555907630487)
  ·
    refine ⟨56283732917141333861445731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37522488611427555907630487 56283732917141333861445731)
    ·
      refine ⟨84425599375712000792168597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56283732917141333861445731 84425599375712000792168597)
      ·
        refine ⟨3957449970736500037132903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 84425599375712000792168597 3957449970736500037132903)
        ·
          refine ⟨5936174956104750055699355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3957449970736500037132903 5936174956104750055699355)
          ·
            refine ⟨8904262434157125083549033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5936174956104750055699355 8904262434157125083549033)
            ·
              refine ⟨6678196825617843812661775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8904262434157125083549033 6678196825617843812661775)
              ·
                refine ⟨10017295238426765718992663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6678196825617843812661775 10017295238426765718992663)
                ·
                  refine ⟨15025942857640148578488995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10017295238426765718992663 15025942857640148578488995)
                  ·
                    refine ⟨22538914286460222867733493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15025942857640148578488995 22538914286460222867733493)
                    ·
                      refine ⟨2113023214355645893850015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22538914286460222867733493 2113023214355645893850015)
                      ·
                        rfl

theorem cell23_4115098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 2, 1, 1, 1, 5].length) (baseStart_4115098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4115098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4115098 prefixEnd_4115098 := by exact prefixLift 4115098
  have htrace : WordTrace (prefixWord ++ tailWord_4115098) baseStart_4115098 baseEnd_4115098 := by
    simpa [prefixWord, tailWord_4115098, baseEnd_4115098] using wordTrace_append hprefix tailTrace_4115098
  have hstable : (prefixWord ++ tailWord_4115098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4115098).length < 2 ^ (prefixWord ++ tailWord_4115098).sum := by decide
  have hdescent : baseEnd_4115098 < baseStart_4115098 := by decide
  rcases family_descends (prefixWord ++ tailWord_4115098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4115171 : List Nat := [1, 1, 1, 7, 1, 1, 1, 1, 2, 4, 3]
def baseStart_4115171 : Nat := 118140960795 + 4115171 * 2 ^ 59
def prefixEnd_4115171 : Nat := 4983230072969 + 3 ^ 40 * 4115171 * 2
def baseEnd_4115171 : Nat := 2113060698443424108237179

theorem tailTrace_4115171 : CollatzResearch.WordTrace tailWord_4115171 prefixEnd_4115171 2113060698443424108237179 := by
  unfold tailWord_4115171
  simp only [CollatzResearch.WordTrace]
  refine ⟨150092616974445757097929367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100061744649630504731952911 150092616974445757097929367)
  ·
    refine ⟨225138925461668635646894051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150092616974445757097929367 225138925461668635646894051)
    ·
      refine ⟨337708388192502953470341077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225138925461668635646894051 337708388192502953470341077)
      ·
        refine ⟨7915040348261787971961119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 337708388192502953470341077 7915040348261787971961119)
        ·
          refine ⟨11872560522392681957941679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7915040348261787971961119 11872560522392681957941679)
          ·
            refine ⟨17808840783589022936912519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11872560522392681957941679 17808840783589022936912519)
            ·
              refine ⟨26713261175383534405368779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17808840783589022936912519 26713261175383534405368779)
              ·
                refine ⟨40069891763075301608053169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26713261175383534405368779 40069891763075301608053169)
                ·
                  refine ⟨30052418822306476206039877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40069891763075301608053169 30052418822306476206039877)
                  ·
                    refine ⟨5634828529182464288632477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30052418822306476206039877 5634828529182464288632477)
                    ·
                      refine ⟨2113060698443424108237179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5634828529182464288632477 2113060698443424108237179)
                      ·
                        rfl

theorem cell23_4115171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 1, 1, 2, 4, 3].length) (baseStart_4115171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4115171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4115171 prefixEnd_4115171 := by exact prefixLift 4115171
  have htrace : WordTrace (prefixWord ++ tailWord_4115171) baseStart_4115171 baseEnd_4115171 := by
    simpa [prefixWord, tailWord_4115171, baseEnd_4115171] using wordTrace_append hprefix tailTrace_4115171
  have hstable : (prefixWord ++ tailWord_4115171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4115171).length < 2 ^ (prefixWord ++ tailWord_4115171).sum := by decide
  have hdescent : baseEnd_4115171 < baseStart_4115171 := by decide
  rcases family_descends (prefixWord ++ tailWord_4115171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4115181 : List Nat := [1, 5, 1, 2, 1, 1, 3, 1, 2, 2, 4]
def baseStart_4115181 : Nat := 118140960795 + 4115181 * 2 ^ 59
def prefixEnd_4115181 : Nat := 4983230072969 + 3 ^ 40 * 4115181 * 2
def baseEnd_4115181 : Nat := 2113065833249969069112133

theorem tailTrace_4115181 : CollatzResearch.WordTrace tailWord_4115181 prefixEnd_4115181 2113065833249969069112133 := by
  unfold tailWord_4115181
  simp only [CollatzResearch.WordTrace]
  refine ⟨150092981704409528805793397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100061987802939685870528931 150092981704409528805793397)
  ·
    refine ⟨14071217034788393325543131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 150092981704409528805793397 14071217034788393325543131)
    ·
      refine ⟨21106825552182589988314697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14071217034788393325543131 21106825552182589988314697)
      ·
        refine ⟨15830119164136942491236023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21106825552182589988314697 15830119164136942491236023)
        ·
          refine ⟨23745178746205413736854035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15830119164136942491236023 23745178746205413736854035)
          ·
            refine ⟨35617768119308120605281053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23745178746205413736854035 35617768119308120605281053)
            ·
              refine ⟨13356663044740545226980395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35617768119308120605281053 13356663044740545226980395)
              ·
                refine ⟨20034994567110817840470593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13356663044740545226980395 20034994567110817840470593)
                ·
                  refine ⟨15026245925333113380352945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20034994567110817840470593 15026245925333113380352945)
                  ·
                    refine ⟨11269684443999835035264709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15026245925333113380352945 11269684443999835035264709)
                    ·
                      refine ⟨2113065833249969069112133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11269684443999835035264709 2113065833249969069112133)
                      ·
                        rfl

theorem cell23_4115181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 3, 1, 2, 2, 4].length) (baseStart_4115181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4115181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4115181 prefixEnd_4115181 := by exact prefixLift 4115181
  have htrace : WordTrace (prefixWord ++ tailWord_4115181) baseStart_4115181 baseEnd_4115181 := by
    simpa [prefixWord, tailWord_4115181, baseEnd_4115181] using wordTrace_append hprefix tailTrace_4115181
  have hstable : (prefixWord ++ tailWord_4115181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4115181).length < 2 ^ (prefixWord ++ tailWord_4115181).sum := by decide
  have hdescent : baseEnd_4115181 < baseStart_4115181 := by decide
  rcases family_descends (prefixWord ++ tailWord_4115181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4115208 : List Nat := [2, 1, 3, 2, 2, 3, 2, 3, 5]
def baseStart_4115208 : Nat := 118140960795 + 4115208 * 2 ^ 59
def prefixEnd_4115208 : Nat := 4983230072969 + 3 ^ 40 * 4115208 * 2
def baseEnd_4115208 : Nat := 234786633025293384830501

theorem tailTrace_4115208 : CollatzResearch.WordTrace tailWord_4115208 prefixEnd_4115208 234786633025293384830501 := by
  unfold tailWord_4115208
  simp only [CollatzResearch.WordTrace]
  refine ⟨75046983237655856208513139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100062644316874474944684185 75046983237655856208513139)
  ·
    refine ⟨112570474856483784312769709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75046983237655856208513139 112570474856483784312769709)
    ·
      refine ⟨42213928071181419117288641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 112570474856483784312769709 42213928071181419117288641)
      ·
        refine ⟨31660446053386064337966481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42213928071181419117288641 31660446053386064337966481)
        ·
          refine ⟨23745334540039548253474861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31660446053386064337966481 23745334540039548253474861)
          ·
            refine ⟨8904500452514830595053073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23745334540039548253474861 8904500452514830595053073)
            ·
              refine ⟨6678375339386122946289805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8904500452514830595053073 6678375339386122946289805)
              ·
                refine ⟨2504390752269796104858677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6678375339386122946289805 2504390752269796104858677)
                ·
                  refine ⟨234786633025293384830501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2504390752269796104858677 234786633025293384830501)
                  ·
                    rfl

theorem cell23_4115208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 2, 3, 5].length) (baseStart_4115208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4115208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4115208 prefixEnd_4115208 := by exact prefixLift 4115208
  have htrace : WordTrace (prefixWord ++ tailWord_4115208) baseStart_4115208 baseEnd_4115208 := by
    simpa [prefixWord, tailWord_4115208, baseEnd_4115208] using wordTrace_append hprefix tailTrace_4115208
  have hstable : (prefixWord ++ tailWord_4115208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4115208).length < 2 ^ (prefixWord ++ tailWord_4115208).sum := by decide
  have hdescent : baseEnd_4115208 < baseStart_4115208 := by decide
  rcases family_descends (prefixWord ++ tailWord_4115208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4115308 : List Nat := [2, 2, 1, 1, 4, 1, 2, 1, 5, 1, 3]
def baseStart_4115308 : Nat := 118140960795 + 4115308 * 2 ^ 59
def prefixEnd_4115308 : Nat := 4983230072969 + 3 ^ 40 * 4115308 * 2
def baseEnd_4115308 : Nat := 2113131045293090072224049

theorem tailTrace_4115308 : CollatzResearch.WordTrace tailWord_4115308 prefixEnd_4115308 2113131045293090072224049 := by
  unfold tailWord_4115308
  simp only [CollatzResearch.WordTrace]
  refine ⟨75048806887474714747833289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100065075849966286330444385 75048806887474714747833289)
  ·
    refine ⟨56286605165606036060874967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75048806887474714747833289 56286605165606036060874967)
    ·
      refine ⟨84429907748409054091312451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56286605165606036060874967 84429907748409054091312451)
      ·
        refine ⟨126644861622613581136968677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84429907748409054091312451 126644861622613581136968677)
        ·
          refine ⟨23745911554240046463181627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 126644861622613581136968677 23745911554240046463181627)
          ·
            refine ⟨35618867331360069694772441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23745911554240046463181627 35618867331360069694772441)
            ·
              refine ⟨26714150498520052271079331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35618867331360069694772441 26714150498520052271079331)
              ·
                refine ⟨40071225747780078406618997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26714150498520052271079331 40071225747780078406618997)
                ·
                  refine ⟨3756677413854382350620531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 40071225747780078406618997 3756677413854382350620531)
                  ·
                    refine ⟨5635016120781573525930797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3756677413854382350620531 5635016120781573525930797)
                    ·
                      refine ⟨2113131045293090072224049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5635016120781573525930797 2113131045293090072224049)
                      ·
                        rfl

theorem cell23_4115308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 5, 1, 3].length) (baseStart_4115308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4115308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4115308 prefixEnd_4115308 := by exact prefixLift 4115308
  have htrace : WordTrace (prefixWord ++ tailWord_4115308) baseStart_4115308 baseEnd_4115308 := by
    simpa [prefixWord, tailWord_4115308, baseEnd_4115308] using wordTrace_append hprefix tailTrace_4115308
  have hstable : (prefixWord ++ tailWord_4115308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4115308).length < 2 ^ (prefixWord ++ tailWord_4115308).sum := by decide
  have hdescent : baseEnd_4115308 < baseStart_4115308 := by decide
  rcases family_descends (prefixWord ++ tailWord_4115308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4115335 : List Nat := [1, 1, 4, 2, 3, 1, 2, 2, 2, 3, 2]
def baseStart_4115335 : Nat := 118140960795 + 4115335 * 2 ^ 59
def prefixEnd_4115335 : Nat := 4983230072969 + 3 ^ 40 * 4115335 * 2
def baseEnd_4115335 : Nat := 2113144909270761466586425

theorem tailTrace_4115335 : CollatzResearch.WordTrace tailWord_4115335 prefixEnd_4115335 2113144909270761466586425 := by
  unfold tailWord_4115335
  simp only [CollatzResearch.WordTrace]
  refine ⟨150098598545851613106899459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100065732363901075404599639 150098598545851613106899459)
  ·
    refine ⟨225147897818777419660349189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150098598545851613106899459 225147897818777419660349189)
    ·
      refine ⟨42215230841020766186315473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 225147897818777419660349189 42215230841020766186315473)
      ·
        refine ⟨31661423130765574639736605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42215230841020766186315473 31661423130765574639736605)
        ·
          refine ⟨11873033674037090489901227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31661423130765574639736605 11873033674037090489901227)
          ·
            refine ⟨17809550511055635734851841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11873033674037090489901227 17809550511055635734851841)
            ·
              refine ⟨13357162883291726801138881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17809550511055635734851841 13357162883291726801138881)
              ·
                refine ⟨10017872162468795100854161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13357162883291726801138881 10017872162468795100854161)
                ·
                  refine ⟨7513404121851596325640621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10017872162468795100854161 7513404121851596325640621)
                  ·
                    refine ⟨2817526545694348622115233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7513404121851596325640621 2817526545694348622115233)
                    ·
                      refine ⟨2113144909270761466586425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2817526545694348622115233 2113144909270761466586425)
                      ·
                        rfl

theorem cell23_4115335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 2, 2, 2, 3, 2].length) (baseStart_4115335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4115335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4115335 prefixEnd_4115335 := by exact prefixLift 4115335
  have htrace : WordTrace (prefixWord ++ tailWord_4115335) baseStart_4115335 baseEnd_4115335 := by
    simpa [prefixWord, tailWord_4115335, baseEnd_4115335] using wordTrace_append hprefix tailTrace_4115335
  have hstable : (prefixWord ++ tailWord_4115335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4115335).length < 2 ^ (prefixWord ++ tailWord_4115335).sum := by decide
  have hdescent : baseEnd_4115335 < baseStart_4115335 := by decide
  rcases family_descends (prefixWord ++ tailWord_4115335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4115348 : List Nat := [2, 4, 2, 1, 1, 1, 1, 1, 5, 1, 4]
def baseStart_4115348 : Nat := 118140960795 + 4115348 * 2 ^ 59
def prefixEnd_4115348 : Nat := 4983230072969 + 3 ^ 40 * 4115348 * 2
def baseEnd_4115348 : Nat := 2113151584519269915723865

theorem tailTrace_4115348 : CollatzResearch.WordTrace tailWord_4115348 prefixEnd_4115348 2113151584519269915723865 := by
  unfold tailWord_4115348
  simp only [CollatzResearch.WordTrace]
  refine ⟨75049536347402258163561349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100066048463203010884748465 75049536347402258163561349)
  ·
    refine ⟨14071788065137923405667753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 75049536347402258163561349 14071788065137923405667753)
    ·
      refine ⟨10553841048853442554250815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14071788065137923405667753 10553841048853442554250815)
      ·
        refine ⟨15830761573280163831376223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10553841048853442554250815 15830761573280163831376223)
        ·
          refine ⟨23746142359920245747064335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15830761573280163831376223 23746142359920245747064335)
          ·
            refine ⟨35619213539880368620596503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23746142359920245747064335 35619213539880368620596503)
            ·
              refine ⟨53428820309820552930894755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35619213539880368620596503 53428820309820552930894755)
              ·
                refine ⟨80143230464730829396342133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53428820309820552930894755 80143230464730829396342133)
                ·
                  refine ⟨7513427856068515255907075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 80143230464730829396342133 7513427856068515255907075)
                  ·
                    refine ⟨11270141784102772883860613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7513427856068515255907075 11270141784102772883860613)
                    ·
                      refine ⟨2113151584519269915723865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11270141784102772883860613 2113151584519269915723865)
                      ·
                        rfl

theorem cell23_4115348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 1, 5, 1, 4].length) (baseStart_4115348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4115348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4115348 prefixEnd_4115348 := by exact prefixLift 4115348
  have htrace : WordTrace (prefixWord ++ tailWord_4115348) baseStart_4115348 baseEnd_4115348 := by
    simpa [prefixWord, tailWord_4115348, baseEnd_4115348] using wordTrace_append hprefix tailTrace_4115348
  have hstable : (prefixWord ++ tailWord_4115348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4115348).length < 2 ^ (prefixWord ++ tailWord_4115348).sum := by decide
  have hdescent : baseEnd_4115348 < baseStart_4115348 := by decide
  rcases family_descends (prefixWord ++ tailWord_4115348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4115351 : List Nat := [1, 1, 3, 3, 1, 2, 2, 1, 3, 1, 5]
def baseStart_4115351 : Nat := 118140960795 + 4115351 * 2 ^ 59
def prefixEnd_4115351 : Nat := 4983230072969 + 3 ^ 40 * 4115351 * 2
def baseEnd_4115351 : Nat := 2113153124961233403986351

theorem tailTrace_4115351 : CollatzResearch.WordTrace tailWord_4115351 prefixEnd_4115351 2113153124961233403986351 := by
  unfold tailWord_4115351
  simp only [CollatzResearch.WordTrace]
  refine ⟨150099182113793647839481907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100066121409195765226321271 150099182113793647839481907)
  ·
    refine ⟨225148773170690471759222861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150099182113793647839481907 225148773170690471759222861)
    ·
      refine ⟨84430789939008926909708573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 225148773170690471759222861 84430789939008926909708573)
      ·
        refine ⟨31661546227128347591140715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84430789939008926909708573 31661546227128347591140715)
        ·
          refine ⟨47492319340692521386711073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31661546227128347591140715 47492319340692521386711073)
          ·
            refine ⟨35619239505519391040033305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47492319340692521386711073 35619239505519391040033305)
            ·
              refine ⟨26714429629139543280024979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35619239505519391040033305 26714429629139543280024979)
              ·
                refine ⟨40071644443709314920037469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26714429629139543280024979 40071644443709314920037469)
                ·
                  refine ⟨15026866666390993095014051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40071644443709314920037469 15026866666390993095014051)
                  ·
                    refine ⟨22540299999586489642521077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15026866666390993095014051 22540299999586489642521077)
                    ·
                      refine ⟨2113153124961233403986351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22540299999586489642521077 2113153124961233403986351)
                      ·
                        rfl

theorem cell23_4115351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 2, 1, 3, 1, 5].length) (baseStart_4115351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4115351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4115351 prefixEnd_4115351 := by exact prefixLift 4115351
  have htrace : WordTrace (prefixWord ++ tailWord_4115351) baseStart_4115351 baseEnd_4115351 := by
    simpa [prefixWord, tailWord_4115351, baseEnd_4115351] using wordTrace_append hprefix tailTrace_4115351
  have hstable : (prefixWord ++ tailWord_4115351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4115351).length < 2 ^ (prefixWord ++ tailWord_4115351).sum := by decide
  have hdescent : baseEnd_4115351 < baseStart_4115351 := by decide
  rcases family_descends (prefixWord ++ tailWord_4115351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4115385 : List Nat := [1, 2, 1, 4, 2, 3, 1, 3, 1, 2, 3]
def baseStart_4115385 : Nat := 118140960795 + 4115385 * 2 ^ 59
def prefixEnd_4115385 : Nat := 4983230072969 + 3 ^ 40 * 4115385 * 2
def baseEnd_4115385 : Nat := 2113170583303486270961195

theorem tailTrace_4115385 : CollatzResearch.WordTrace tailWord_4115385 prefixEnd_4115385 2113170583303486270961195 := by
  unfold tailWord_4115385
  simp only [CollatzResearch.WordTrace]
  refine ⟨150100422195670471646219609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100066948130446981097479739 150100422195670471646219609)
  ·
    refine ⟨112575316646752853734664707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150100422195670471646219609 112575316646752853734664707)
    ·
      refine ⟨168862974970129280601997061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112575316646752853734664707 168862974970129280601997061)
      ·
        refine ⟨31661807806899240112874449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 168862974970129280601997061 31661807806899240112874449)
        ·
          refine ⟨23746355855174430084655837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31661807806899240112874449 23746355855174430084655837)
          ·
            refine ⟨8904883445690411281745939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23746355855174430084655837 8904883445690411281745939)
            ·
              refine ⟨13357325168535616922618909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8904883445690411281745939 13357325168535616922618909)
              ·
                refine ⟨5008996938200856345982091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13357325168535616922618909 5008996938200856345982091)
                ·
                  refine ⟨7513495407301284518973137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5008996938200856345982091 7513495407301284518973137)
                  ·
                    refine ⟨5635121555475963389229853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7513495407301284518973137 5635121555475963389229853)
                    ·
                      refine ⟨2113170583303486270961195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5635121555475963389229853 2113170583303486270961195)
                      ·
                        rfl

theorem cell23_4115385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 1, 3, 1, 2, 3].length) (baseStart_4115385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4115385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4115385 prefixEnd_4115385 := by exact prefixLift 4115385
  have htrace : WordTrace (prefixWord ++ tailWord_4115385) baseStart_4115385 baseEnd_4115385 := by
    simpa [prefixWord, tailWord_4115385, baseEnd_4115385] using wordTrace_append hprefix tailTrace_4115385
  have hstable : (prefixWord ++ tailWord_4115385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4115385).length < 2 ^ (prefixWord ++ tailWord_4115385).sum := by decide
  have hdescent : baseEnd_4115385 < baseStart_4115385 := by decide
  rcases family_descends (prefixWord ++ tailWord_4115385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4115512 : List Nat := [2, 1, 2, 1, 5, 1, 4, 2, 5]
def baseStart_4115512 : Nat := 118140960795 + 4115512 * 2 ^ 59
def prefixEnd_4115512 : Nat := 4983230072969 + 3 ^ 40 * 4115512 * 2
def baseEnd_4115512 : Nat := 234803977260734141563679

theorem tailTrace_4115512 : CollatzResearch.WordTrace tailWord_4115512 prefixEnd_4115512 234803977260734141563679 := by
  unfold tailWord_4115512
  simp only [CollatzResearch.WordTrace]
  refine ⟨75052527133105186168046395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100070036177473581557395193 75052527133105186168046395)
  ·
    refine ⟨112578790699657779252069593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75052527133105186168046395 112578790699657779252069593)
    ·
      refine ⟨84434093024743334439052195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112578790699657779252069593 84434093024743334439052195)
      ·
        refine ⟨126651139537115001658578293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84434093024743334439052195 126651139537115001658578293)
        ·
          refine ⟨11873544331604531405491715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 126651139537115001658578293 11873544331604531405491715)
          ·
            refine ⟨17810316497406797108237573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11873544331604531405491715 17810316497406797108237573)
            ·
              refine ⟨3339434343263774457794545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17810316497406797108237573 3339434343263774457794545)
              ·
                refine ⟨2504575757447830843345909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3339434343263774457794545 2504575757447830843345909)
                ·
                  refine ⟨234803977260734141563679, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2504575757447830843345909 234803977260734141563679)
                  ·
                    rfl

theorem cell23_4115512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 4, 2, 5].length) (baseStart_4115512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4115512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4115512 prefixEnd_4115512 := by exact prefixLift 4115512
  have htrace : WordTrace (prefixWord ++ tailWord_4115512) baseStart_4115512 baseEnd_4115512 := by
    simpa [prefixWord, tailWord_4115512, baseEnd_4115512] using wordTrace_append hprefix tailTrace_4115512
  have hstable : (prefixWord ++ tailWord_4115512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4115512).length < 2 ^ (prefixWord ++ tailWord_4115512).sum := by decide
  have hdescent : baseEnd_4115512 < baseStart_4115512 := by decide
  rcases family_descends (prefixWord ++ tailWord_4115512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4115528 : List Nat := [2, 1, 3, 1, 1, 1, 4, 2, 1, 3, 4]
def baseStart_4115528 : Nat := 118140960795 + 4115528 * 2 ^ 59
def prefixEnd_4115528 : Nat := 4983230072969 + 3 ^ 40 * 4115528 * 2
def baseEnd_4115528 : Nat := 2113244011037079211473037

theorem tailTrace_4115528 : CollatzResearch.WordTrace tailWord_4115528 prefixEnd_4115528 2113244011037079211473037 := by
  unfold tailWord_4115528
  simp only [CollatzResearch.WordTrace]
  refine ⟨75052818917076203534337619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100070425222768271379116825 75052818917076203534337619)
  ·
    refine ⟨112579228375614305301506429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75052818917076203534337619 112579228375614305301506429)
    ·
      refine ⟨42217210640855364488064911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 112579228375614305301506429 42217210640855364488064911)
      ·
        refine ⟨63325815961283046732097367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42217210640855364488064911 63325815961283046732097367)
        ·
          refine ⟨94988723941924570098146051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63325815961283046732097367 94988723941924570098146051)
          ·
            refine ⟨142483085912886855147219077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94988723941924570098146051 142483085912886855147219077)
            ·
              refine ⟨26715578608666285340103577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 142483085912886855147219077 26715578608666285340103577)
              ·
                refine ⟨20036683956499714005077683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26715578608666285340103577 20036683956499714005077683)
                ·
                  refine ⟨30055025934749571007616525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20036683956499714005077683 30055025934749571007616525)
                  ·
                    refine ⟨11270634725531089127856197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30055025934749571007616525 11270634725531089127856197)
                    ·
                      refine ⟨2113244011037079211473037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11270634725531089127856197 2113244011037079211473037)
                      ·
                        rfl

theorem cell23_4115528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 4, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 4, 2, 1, 3, 4].length) (baseStart_4115528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4115528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4115528 prefixEnd_4115528 := by exact prefixLift 4115528
  have htrace : WordTrace (prefixWord ++ tailWord_4115528) baseStart_4115528 baseEnd_4115528 := by
    simpa [prefixWord, tailWord_4115528, baseEnd_4115528] using wordTrace_append hprefix tailTrace_4115528
  have hstable : (prefixWord ++ tailWord_4115528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4115528).length < 2 ^ (prefixWord ++ tailWord_4115528).sum := by decide
  have hdescent : baseEnd_4115528 < baseStart_4115528 := by decide
  rcases family_descends (prefixWord ++ tailWord_4115528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4115562 : List Nat := [3, 1, 3, 2, 2, 1, 1, 2, 2, 4, 2]
def baseStart_4115562 : Nat := 118140960795 + 4115562 * 2 ^ 59
def prefixEnd_4115562 : Nat := 4983230072969 + 3 ^ 40 * 4115562 * 2
def baseEnd_4115562 : Nat := 2113261469379332078447881

theorem tailTrace_4115562 : CollatzResearch.WordTrace tailWord_4115562 prefixEnd_4115562 2113261469379332078447881 := by
  unfold tailWord_4115562
  simp only [CollatzResearch.WordTrace]
  refine ⟨37526719479007307718853235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100071251944019487250275293 37526719479007307718853235)
  ·
    refine ⟨56290079218510961578279853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37526719479007307718853235 56290079218510961578279853)
    ·
      refine ⟨21108779706941610591854945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56290079218510961578279853 21108779706941610591854945)
      ·
        refine ⟨15831584780206207943891209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21108779706941610591854945 15831584780206207943891209)
        ·
          refine ⟨11873688585154655957918407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15831584780206207943891209 11873688585154655957918407)
          ·
            refine ⟨17810532877731983936877611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11873688585154655957918407 17810532877731983936877611)
            ·
              refine ⟨26715799316597975905316417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17810532877731983936877611 26715799316597975905316417)
              ·
                refine ⟨20036849487448481928987313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26715799316597975905316417 20036849487448481928987313)
                ·
                  refine ⟨15027637115586361446740485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20036849487448481928987313 15027637115586361446740485)
                  ·
                    refine ⟨2817681959172442771263841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15027637115586361446740485 2817681959172442771263841)
                    ·
                      refine ⟨2113261469379332078447881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2817681959172442771263841 2113261469379332078447881)
                      ·
                        rfl

theorem cell23_4115562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 1, 2, 2, 4, 2].length) (baseStart_4115562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4115562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4115562 prefixEnd_4115562 := by exact prefixLift 4115562
  have htrace : WordTrace (prefixWord ++ tailWord_4115562) baseStart_4115562 baseEnd_4115562 := by
    simpa [prefixWord, tailWord_4115562, baseEnd_4115562] using wordTrace_append hprefix tailTrace_4115562
  have hstable : (prefixWord ++ tailWord_4115562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4115562).length < 2 ^ (prefixWord ++ tailWord_4115562).sum := by decide
  have hdescent : baseEnd_4115562 < baseStart_4115562 := by decide
  rcases family_descends (prefixWord ++ tailWord_4115562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4115568 : List Nat := [2, 1, 1, 1, 5, 1, 3, 1, 8]
def baseStart_4115568 : Nat := 118140960795 + 4115568 * 2 ^ 59
def prefixEnd_4115568 : Nat := 4983230072969 + 3 ^ 40 * 4115568 * 2
def baseEnd_4115568 : Nat := 234807172251473228330317

theorem tailTrace_4115568 : CollatzResearch.WordTrace tailWord_4115568 prefixEnd_4115568 234807172251473228330317 := by
  unfold tailWord_4115568
  simp only [CollatzResearch.WordTrace]
  refine ⟨75053548377003746950065679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100071397836004995933420905 75053548377003746950065679)
  ·
    refine ⟨112580322565505620425098519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75053548377003746950065679 112580322565505620425098519)
    ·
      refine ⟨168870483848258430637647779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112580322565505620425098519 168870483848258430637647779)
      ·
        refine ⟨253305725772387645956471669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168870483848258430637647779 253305725772387645956471669)
        ·
          refine ⟨23747411791161341808419219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 253305725772387645956471669 23747411791161341808419219)
          ·
            refine ⟨35621117686742012712628829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23747411791161341808419219 35621117686742012712628829)
            ·
              refine ⟨13357919132528254767235811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35621117686742012712628829 13357919132528254767235811)
              ·
                refine ⟨20036878698792382150853717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13357919132528254767235811 20036878698792382150853717)
                ·
                  refine ⟨234807172251473228330317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 20036878698792382150853717 234807172251473228330317)
                  ·
                    rfl

theorem cell23_4115568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 3, 1, 8].length) (baseStart_4115568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4115568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4115568 prefixEnd_4115568 := by exact prefixLift 4115568
  have htrace : WordTrace (prefixWord ++ tailWord_4115568) baseStart_4115568 baseEnd_4115568 := by
    simpa [prefixWord, tailWord_4115568, baseEnd_4115568] using wordTrace_append hprefix tailTrace_4115568
  have hstable : (prefixWord ++ tailWord_4115568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4115568).length < 2 ^ (prefixWord ++ tailWord_4115568).sum := by decide
  have hdescent : baseEnd_4115568 < baseStart_4115568 := by decide
  rcases family_descends (prefixWord ++ tailWord_4115568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4115628 : List Nat := [2, 2, 1, 1, 1, 1, 1, 3, 5, 6]
def baseStart_4115628 : Nat := 118140960795 + 4115628 * 2 ^ 59
def prefixEnd_4115628 : Nat := 4983230072969 + 3 ^ 40 * 4115628 * 2
def baseEnd_4115628 : Nat := 704431786367509606740859

theorem tailTrace_4115628 : CollatzResearch.WordTrace tailWord_4115628 prefixEnd_4115628 704431786367509606740859 := by
  unfold tailWord_4115628
  simp only [CollatzResearch.WordTrace]
  refine ⟨75054642566895062073657769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100072856755860082764877025 75054642566895062073657769)
  ·
    refine ⟨56290981925171296555243327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75054642566895062073657769 56290981925171296555243327)
    ·
      refine ⟨84436472887756944832864991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56290981925171296555243327 84436472887756944832864991)
      ·
        refine ⟨126654709331635417249297487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84436472887756944832864991 126654709331635417249297487)
        ·
          refine ⟨189982063997453125873946231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126654709331635417249297487 189982063997453125873946231)
          ·
            refine ⟨284973095996179688810919347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 189982063997453125873946231 284973095996179688810919347)
            ·
              refine ⟨427459643994269533216379021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 284973095996179688810919347 427459643994269533216379021)
              ·
                refine ⟨160297366497851074956142133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 427459643994269533216379021 160297366497851074956142133)
                ·
                  refine ⟨15027878109173538277138325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 160297366497851074956142133 15027878109173538277138325)
                  ·
                    refine ⟨704431786367509606740859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15027878109173538277138325 704431786367509606740859)
                    ·
                      rfl

theorem cell23_4115628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 6].length) (baseStart_4115628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4115628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4115628 prefixEnd_4115628 := by exact prefixLift 4115628
  have htrace : WordTrace (prefixWord ++ tailWord_4115628) baseStart_4115628 baseEnd_4115628 := by
    simpa [prefixWord, tailWord_4115628, baseEnd_4115628] using wordTrace_append hprefix tailTrace_4115628
  have hstable : (prefixWord ++ tailWord_4115628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4115628).length < 2 ^ (prefixWord ++ tailWord_4115628).sum := by decide
  have hdescent : baseEnd_4115628 < baseStart_4115628 := by decide
  rcases family_descends (prefixWord ++ tailWord_4115628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4115649 : List Nat := [1, 2, 6, 1, 1, 1, 3, 2, 1, 5]
def baseStart_4115649 : Nat := 118140960795 + 4115649 * 2 ^ 59
def prefixEnd_4115649 : Nat := 4983230072969 + 3 ^ 40 * 4115649 * 2
def baseEnd_4115649 : Nat := 704435380732091079353327

theorem tailTrace_4115649 : CollatzResearch.WordTrace tailWord_4115649 prefixEnd_4115649 704435380732091079353327 := by
  unfold tailWord_4115649
  simp only [CollatzResearch.WordTrace]
  refine ⟨150110051066714044733830001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100073367377809363155886667 150110051066714044733830001)
  ·
    refine ⟨112582538300035533550372501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150110051066714044733830001 112582538300035533550372501)
    ·
      refine ⟨5277306482814165635173711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 112582538300035533550372501 5277306482814165635173711)
      ·
        refine ⟨7915959724221248452760567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5277306482814165635173711 7915959724221248452760567)
        ·
          refine ⟨11873939586331872679140851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7915959724221248452760567 11873939586331872679140851)
          ·
            refine ⟨17810909379497809018711277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11873939586331872679140851 17810909379497809018711277)
            ·
              refine ⟨6679091017311678382016729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17810909379497809018711277 6679091017311678382016729)
              ·
                refine ⟨5009318262983758786512547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6679091017311678382016729 5009318262983758786512547)
                ·
                  refine ⟨7513977394475638179768821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5009318262983758786512547 7513977394475638179768821)
                  ·
                    refine ⟨704435380732091079353327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7513977394475638179768821 704435380732091079353327)
                    ·
                      rfl

theorem cell23_4115649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 3, 2, 1, 5].length) (baseStart_4115649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4115649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4115649 prefixEnd_4115649 := by exact prefixLift 4115649
  have htrace : WordTrace (prefixWord ++ tailWord_4115649) baseStart_4115649 baseEnd_4115649 := by
    simpa [prefixWord, tailWord_4115649, baseEnd_4115649] using wordTrace_append hprefix tailTrace_4115649
  have hstable : (prefixWord ++ tailWord_4115649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4115649).length < 2 ^ (prefixWord ++ tailWord_4115649).sum := by decide
  have hdescent : baseEnd_4115649 < baseStart_4115649 := by decide
  rcases family_descends (prefixWord ++ tailWord_4115649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4115662 : List Nat := [4, 1, 1, 1, 5, 1, 1, 2, 1, 6]
def baseStart_4115662 : Nat := 118140960795 + 4115662 * 2 ^ 59
def prefixEnd_4115662 : Nat := 4983230072969 + 3 ^ 40 * 4115662 * 2
def baseEnd_4115662 : Nat := 704437605814927229065807

theorem tailTrace_4115662 : CollatzResearch.WordTrace tailWord_4115662 prefixEnd_4115662 704437605814927229065807 := by
  unfold tailWord_4115662
  simp only [CollatzResearch.WordTrace]
  refine ⟨18763815651958368494256655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 100073683477111298636035493 18763815651958368494256655)
  ·
    refine ⟨28145723477937552741384983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18763815651958368494256655 28145723477937552741384983)
    ·
      refine ⟨42218585216906329112077475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28145723477937552741384983 42218585216906329112077475)
      ·
        refine ⟨63327877825359493668116213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42218585216906329112077475 63327877825359493668116213)
        ·
          refine ⟨5936988546127452531385895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 63327877825359493668116213 5936988546127452531385895)
          ·
            refine ⟨8905482819191178797078843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5936988546127452531385895 8905482819191178797078843)
            ·
              refine ⟨13358224228786768195618265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8905482819191178797078843 13358224228786768195618265)
              ·
                refine ⟨10018668171590076146713699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13358224228786768195618265 10018668171590076146713699)
                ·
                  refine ⟨15028002257385114220070549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10018668171590076146713699 15028002257385114220070549)
                  ·
                    refine ⟨704437605814927229065807, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15028002257385114220070549 704437605814927229065807)
                    ·
                      rfl

theorem cell23_4115662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 1, 2, 1, 6].length) (baseStart_4115662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4115662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4115662 prefixEnd_4115662 := by exact prefixLift 4115662
  have htrace : WordTrace (prefixWord ++ tailWord_4115662) baseStart_4115662 baseEnd_4115662 := by
    simpa [prefixWord, tailWord_4115662, baseEnd_4115662] using wordTrace_append hprefix tailTrace_4115662
  have hstable : (prefixWord ++ tailWord_4115662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4115662).length < 2 ^ (prefixWord ++ tailWord_4115662).sum := by decide
  have hdescent : baseEnd_4115662 < baseStart_4115662 := by decide
  rcases family_descends (prefixWord ++ tailWord_4115662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4115729 : List Nat := [1, 2, 2, 1, 1, 4, 3, 3, 1, 3, 2]
def baseStart_4115729 : Nat := 118140960795 + 4115729 * 2 ^ 59
def prefixEnd_4115729 : Nat := 4983230072969 + 3 ^ 40 * 4115729 * 2
def baseEnd_4115729 : Nat := 2113347220648632925059613

theorem tailTrace_4115729 : CollatzResearch.WordTrace tailWord_4115729 prefixEnd_4115729 2113347220648632925059613 := by
  unfold tailWord_4115729
  simp only [CollatzResearch.WordTrace]
  refine ⟨150112968906424218396742241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100075312604282812264494827 150112968906424218396742241)
  ·
    refine ⟨112584726679818163797556681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150112968906424218396742241 112584726679818163797556681)
    ·
      refine ⟨84438545009863622848167511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112584726679818163797556681 84438545009863622848167511)
      ·
        refine ⟨126657817514795434272251267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84438545009863622848167511 126657817514795434272251267)
        ·
          refine ⟨189986726272193151408376901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126657817514795434272251267 189986726272193151408376901)
          ·
            refine ⟨35622511176036215889070669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 189986726272193151408376901 35622511176036215889070669)
            ·
              refine ⟨13358441691013580958401501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35622511176036215889070669 13358441691013580958401501)
              ·
                refine ⟨5009415634130092859400563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13358441691013580958401501 5009415634130092859400563)
                ·
                  refine ⟨7514123451195139289100845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5009415634130092859400563 7514123451195139289100845)
                  ·
                    refine ⟨2817796294198177233412817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7514123451195139289100845 2817796294198177233412817)
                    ·
                      refine ⟨2113347220648632925059613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2817796294198177233412817 2113347220648632925059613)
                      ·
                        rfl

theorem cell23_4115729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 3, 2].length) (baseStart_4115729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4115729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4115729 prefixEnd_4115729 := by exact prefixLift 4115729
  have htrace : WordTrace (prefixWord ++ tailWord_4115729) baseStart_4115729 baseEnd_4115729 := by
    simpa [prefixWord, tailWord_4115729, baseEnd_4115729] using wordTrace_append hprefix tailTrace_4115729
  have hstable : (prefixWord ++ tailWord_4115729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4115729).length < 2 ^ (prefixWord ++ tailWord_4115729).sum := by decide
  have hdescent : baseEnd_4115729 < baseStart_4115729 := by decide
  rcases family_descends (prefixWord ++ tailWord_4115729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4115730 : List Nat := [3, 2, 4, 2, 2, 1, 1, 2, 2, 4]
def baseStart_4115730 : Nat := 118140960795 + 4115730 * 2 ^ 59
def prefixEnd_4115730 : Nat := 4983230072969 + 3 ^ 40 * 4115730 * 2
def baseEnd_4115730 : Nat := 704449244709762473715703

theorem tailTrace_4115730 : CollatzResearch.WordTrace tailWord_4115730 prefixEnd_4115730 704449244709762473715703 := by
  unfold tailWord_4115730
  simp only [CollatzResearch.WordTrace]
  refine ⟨37528251344855148891882161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100075336919613730378352429 37528251344855148891882161)
  ·
    refine ⟨28146188508641361668911621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37528251344855148891882161 28146188508641361668911621)
    ·
      refine ⟨5277410345370255312920929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28146188508641361668911621 5277410345370255312920929)
      ·
        refine ⟨3958057759027691484690697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5277410345370255312920929 3958057759027691484690697)
        ·
          refine ⟨2968543319270768613518023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3958057759027691484690697 2968543319270768613518023)
          ·
            refine ⟨4452814978906152920277035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2968543319270768613518023 4452814978906152920277035)
            ·
              refine ⟨6679222468359229380415553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4452814978906152920277035 6679222468359229380415553)
              ·
                refine ⟨5009416851269422035311665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6679222468359229380415553 5009416851269422035311665)
                ·
                  refine ⟨3757062638452066526483749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5009416851269422035311665 3757062638452066526483749)
                  ·
                    refine ⟨704449244709762473715703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3757062638452066526483749 704449244709762473715703)
                    ·
                      rfl

theorem cell23_4115730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 2, 1, 1, 2, 2, 4].length) (baseStart_4115730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4115730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4115730 prefixEnd_4115730 := by exact prefixLift 4115730
  have htrace : WordTrace (prefixWord ++ tailWord_4115730) baseStart_4115730 baseEnd_4115730 := by
    simpa [prefixWord, tailWord_4115730, baseEnd_4115730] using wordTrace_append hprefix tailTrace_4115730
  have hstable : (prefixWord ++ tailWord_4115730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4115730).length < 2 ^ (prefixWord ++ tailWord_4115730).sum := by decide
  have hdescent : baseEnd_4115730 < baseStart_4115730 := by decide
  rcases family_descends (prefixWord ++ tailWord_4115730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4115735 : List Nat := [1, 1, 3, 4, 1, 1, 1, 1, 4, 6]
def baseStart_4115735 : Nat := 118140960795 + 4115735 * 2 ^ 59
def prefixEnd_4115735 : Nat := 4983230072969 + 3 ^ 40 * 4115735 * 2
def baseEnd_4115735 : Nat := 704450100510853300528195

theorem tailTrace_4115735 : CollatzResearch.WordTrace tailWord_4115735 prefixEnd_4115735 704450100510853300528195 := by
  unfold tailWord_4115735
  simp only [CollatzResearch.WordTrace]
  refine ⟨150113187744402481421460659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100075458496268320947640439 150113187744402481421460659)
  ·
    refine ⟨225169781616603722132190989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150113187744402481421460659 225169781616603722132190989)
    ·
      refine ⟨84438668106226395799571621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 225169781616603722132190989 84438668106226395799571621)
      ·
        refine ⟨15832250269917449212419679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 84438668106226395799571621 15832250269917449212419679)
        ·
          refine ⟨23748375404876173818629519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15832250269917449212419679 23748375404876173818629519)
          ·
            refine ⟨35622563107314260727944279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23748375404876173818629519 35622563107314260727944279)
            ·
              refine ⟨53433844660971391091916419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35622563107314260727944279 53433844660971391091916419)
              ·
                refine ⟨80150766991457086637874629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53433844660971391091916419 80150766991457086637874629)
                ·
                  refine ⟨15028268810898203744601493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 80150766991457086637874629 15028268810898203744601493)
                  ·
                    refine ⟨704450100510853300528195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15028268810898203744601493 704450100510853300528195)
                    ·
                      rfl

theorem cell23_4115735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 1, 4, 6].length) (baseStart_4115735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4115735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4115735 prefixEnd_4115735 := by exact prefixLift 4115735
  have htrace : WordTrace (prefixWord ++ tailWord_4115735) baseStart_4115735 baseEnd_4115735 := by
    simpa [prefixWord, tailWord_4115735, baseEnd_4115735] using wordTrace_append hprefix tailTrace_4115735
  have hstable : (prefixWord ++ tailWord_4115735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4115735).length < 2 ^ (prefixWord ++ tailWord_4115735).sum := by decide
  have hdescent : baseEnd_4115735 < baseStart_4115735 := by decide
  rcases family_descends (prefixWord ++ tailWord_4115735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4115736 : List Nat := [2, 1, 2, 3, 1, 5, 1, 2, 2, 1, 3]
def baseStart_4115736 : Nat := 118140960795 + 4115736 * 2 ^ 59
def prefixEnd_4115736 : Nat := 4983230072969 + 3 ^ 40 * 4115736 * 2
def baseEnd_4115736 : Nat := 2113350815013214397672081

theorem tailTrace_4115736 : CollatzResearch.WordTrace tailWord_4115736 prefixEnd_4115736 2113350815013214397672081 := by
  unfold tailWord_4115736
  simp only [CollatzResearch.WordTrace]
  refine ⟨75056612108699429296123531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100075482811599239061498041 75056612108699429296123531)
  ·
    refine ⟨112584918163049143944185297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75056612108699429296123531 112584918163049143944185297)
    ·
      refine ⟨84438688622286857958138973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112584918163049143944185297 84438688622286857958138973)
      ·
        refine ⟨31664508233357571734302115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84438688622286857958138973 31664508233357571734302115)
        ·
          refine ⟨47496762350036357601453173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31664508233357571734302115 47496762350036357601453173)
          ·
            refine ⟨4452821470315908525136235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 47496762350036357601453173 4452821470315908525136235)
            ·
              refine ⟨6679232205473862787704353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4452821470315908525136235 6679232205473862787704353)
              ·
                refine ⟨5009424154105397090778265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6679232205473862787704353 5009424154105397090778265)
                ·
                  refine ⟨3757068115579047818083699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5009424154105397090778265 3757068115579047818083699)
                  ·
                    refine ⟨5635602173368571727125549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3757068115579047818083699 5635602173368571727125549)
                    ·
                      refine ⟨2113350815013214397672081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5635602173368571727125549 2113350815013214397672081)
                      ·
                        rfl

theorem cell23_4115736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 5, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 5, 1, 2, 2, 1, 3].length) (baseStart_4115736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4115736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4115736 prefixEnd_4115736 := by exact prefixLift 4115736
  have htrace : WordTrace (prefixWord ++ tailWord_4115736) baseStart_4115736 baseEnd_4115736 := by
    simpa [prefixWord, tailWord_4115736, baseEnd_4115736] using wordTrace_append hprefix tailTrace_4115736
  have hstable : (prefixWord ++ tailWord_4115736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4115736).length < 2 ^ (prefixWord ++ tailWord_4115736).sum := by decide
  have hdescent : baseEnd_4115736 < baseStart_4115736 := by decide
  rcases family_descends (prefixWord ++ tailWord_4115736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4115745 : List Nat := [1, 2, 3, 2, 1, 1, 1, 2, 4, 1, 5]
def baseStart_4115745 : Nat := 118140960795 + 4115745 * 2 ^ 59
def prefixEnd_4115745 : Nat := 4983230072969 + 3 ^ 40 * 4115745 * 2
def baseEnd_4115745 : Nat := 2113355436339104862459539

theorem tailTrace_4115745 : CollatzResearch.WordTrace tailWord_4115745 prefixEnd_4115745 2113355436339104862459539 := by
  unfold tailWord_4115745
  simp only [CollatzResearch.WordTrace]
  refine ⟨150113552474366253129324689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100075701649577502086216459 150113552474366253129324689)
  ·
    refine ⟨112585164355774689846993517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150113552474366253129324689 112585164355774689846993517)
    ·
      refine ⟨42219436633415508692622569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 112585164355774689846993517 42219436633415508692622569)
      ·
        refine ⟨31664577475061631519466927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42219436633415508692622569 31664577475061631519466927)
        ·
          refine ⟨47496866212592447279200391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31664577475061631519466927 47496866212592447279200391)
          ·
            refine ⟨71245299318888670918800587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47496866212592447279200391 71245299318888670918800587)
            ·
              refine ⟨106867948978333006378200881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71245299318888670918800587 106867948978333006378200881)
              ·
                refine ⟨80150961733749754783650661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 106867948978333006378200881 80150961733749754783650661)
                ·
                  refine ⟨15028305325078079021934499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 80150961733749754783650661 15028305325078079021934499)
                  ·
                    refine ⟨22542457987617118532901749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15028305325078079021934499 22542457987617118532901749)
                    ·
                      refine ⟨2113355436339104862459539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22542457987617118532901749 2113355436339104862459539)
                      ·
                        rfl

theorem cell23_4115745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 2, 4, 1, 5].length) (baseStart_4115745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4115745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4115745 prefixEnd_4115745 := by exact prefixLift 4115745
  have htrace : WordTrace (prefixWord ++ tailWord_4115745) baseStart_4115745 baseEnd_4115745 := by
    simpa [prefixWord, tailWord_4115745, baseEnd_4115745] using wordTrace_append hprefix tailTrace_4115745
  have hstable : (prefixWord ++ tailWord_4115745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4115745).length < 2 ^ (prefixWord ++ tailWord_4115745).sum := by decide
  have hdescent : baseEnd_4115745 < baseStart_4115745 := by decide
  rcases family_descends (prefixWord ++ tailWord_4115745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4115752 : List Nat := [2, 1, 5, 1, 2, 1, 2, 1, 2, 6]
def baseStart_4115752 : Nat := 118140960795 + 4115752 * 2 ^ 59
def prefixEnd_4115752 : Nat := 4983230072969 + 3 ^ 40 * 4115752 * 2
def baseEnd_4115752 : Nat := 704453010234562111690669

theorem tailTrace_4115752 : CollatzResearch.WordTrace tailWord_4115752 prefixEnd_4115752 704453010234562111690669 := by
  unfold tailWord_4115752
  simp only [CollatzResearch.WordTrace]
  refine ⟨75056903892670446662414755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100075871856893928883219673 75056903892670446662414755)
  ·
    refine ⟨112585355839005669993622133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75056903892670446662414755 112585355839005669993622133)
    ·
      refine ⟨10554877109906781561902075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 112585355839005669993622133 10554877109906781561902075)
      ·
        refine ⟨15832315664860172342853113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10554877109906781561902075 15832315664860172342853113)
        ·
          refine ⟨11874236748645129257139835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15832315664860172342853113 11874236748645129257139835)
          ·
            refine ⟨17811355122967693885709753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11874236748645129257139835 17811355122967693885709753)
            ·
              refine ⟨13358516342225770414282315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17811355122967693885709753 13358516342225770414282315)
              ·
                refine ⟨20037774513338655621423473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13358516342225770414282315 20037774513338655621423473)
                ·
                  refine ⟨15028330885003991716067605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20037774513338655621423473 15028330885003991716067605)
                  ·
                    refine ⟨704453010234562111690669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15028330885003991716067605 704453010234562111690669)
                    ·
                      rfl

theorem cell23_4115752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 2, 1, 2, 6].length) (baseStart_4115752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4115752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4115752 prefixEnd_4115752 := by exact prefixLift 4115752
  have htrace : WordTrace (prefixWord ++ tailWord_4115752) baseStart_4115752 baseEnd_4115752 := by
    simpa [prefixWord, tailWord_4115752, baseEnd_4115752] using wordTrace_append hprefix tailTrace_4115752
  have hstable : (prefixWord ++ tailWord_4115752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4115752).length < 2 ^ (prefixWord ++ tailWord_4115752).sum := by decide
  have hdescent : baseEnd_4115752 < baseStart_4115752 := by decide
  rcases family_descends (prefixWord ++ tailWord_4115752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4115825 : List Nat := [1, 2, 2, 2, 1, 2, 2, 1, 2, 8]
def baseStart_4115825 : Nat := 118140960795 + 4115825 * 2 ^ 59
def prefixEnd_4115825 : Nat := 4983230072969 + 3 ^ 40 * 4115825 * 2
def baseEnd_4115825 : Nat := 704465504930488183153057

theorem tailTrace_4115825 : CollatzResearch.WordTrace tailWord_4115825 prefixEnd_4115825 704465504930488183153057 := by
  unfold tailWord_4115825
  simp only [CollatzResearch.WordTrace]
  refine ⟨150116470314076426792236929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100077646876050951194824619 150116470314076426792236929)
  ·
    refine ⟨112587352735557320094177697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150116470314076426792236929 112587352735557320094177697)
    ·
      refine ⟨84440514551667990070633273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112587352735557320094177697 84440514551667990070633273)
      ·
        refine ⟨63330385913750992552974955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84440514551667990070633273 63330385913750992552974955)
        ·
          refine ⟨94995578870626488829462433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63330385913750992552974955 94995578870626488829462433)
          ·
            refine ⟨71246684152969866622096825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94995578870626488829462433 71246684152969866622096825)
            ·
              refine ⟨53435013114727399966572619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71246684152969866622096825 53435013114727399966572619)
              ·
                refine ⟨80152519672091099949858929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53435013114727399966572619 80152519672091099949858929)
                ·
                  refine ⟨60114389754068324962394197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 80152519672091099949858929 60114389754068324962394197)
                  ·
                    refine ⟨704465504930488183153057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 60114389754068324962394197 704465504930488183153057)
                    ·
                      rfl

theorem cell23_4115825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 1, 2, 8].length) (baseStart_4115825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4115825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4115825 prefixEnd_4115825 := by exact prefixLift 4115825
  have htrace : WordTrace (prefixWord ++ tailWord_4115825) baseStart_4115825 baseEnd_4115825 := by
    simpa [prefixWord, tailWord_4115825, baseEnd_4115825] using wordTrace_append hprefix tailTrace_4115825
  have hstable : (prefixWord ++ tailWord_4115825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4115825).length < 2 ^ (prefixWord ++ tailWord_4115825).sum := by decide
  have hdescent : baseEnd_4115825 < baseStart_4115825 := by decide
  rcases family_descends (prefixWord ++ tailWord_4115825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4115872 : List Nat := [2, 1, 1, 4, 1, 2, 1, 5, 6]
def baseStart_4115872 : Nat := 118140960795 + 4115872 * 2 ^ 59
def prefixEnd_4115872 : Nat := 4983230072969 + 3 ^ 40 * 4115872 * 2
def baseEnd_4115872 : Nat := 234824516486913985063495

theorem tailTrace_4115872 : CollatzResearch.WordTrace tailWord_4115872 prefixEnd_4115872 234824516486913985063495 := by
  unfold tailWord_4115872
  simp only [CollatzResearch.WordTrace]
  refine ⟨75059092272453076909598935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100078789696604102546131913 75059092272453076909598935)
  ·
    refine ⟨112588638408679615364398403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75059092272453076909598935 112588638408679615364398403)
    ·
      refine ⟨168882957613019423046597605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112588638408679615364398403 168882957613019423046597605)
      ·
        refine ⟨31665554552441141821237051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 168882957613019423046597605 31665554552441141821237051)
        ·
          refine ⟨47498331828661712731855577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31665554552441141821237051 47498331828661712731855577)
          ·
            refine ⟨35623748871496284548891683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47498331828661712731855577 35623748871496284548891683)
            ·
              refine ⟨53435623307244426823337525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35623748871496284548891683 53435623307244426823337525)
              ·
                refine ⟨5009589685054165014687893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 53435623307244426823337525 5009589685054165014687893)
                ·
                  refine ⟨234824516486913985063495, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5009589685054165014687893 234824516486913985063495)
                  ·
                    rfl

theorem cell23_4115872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 5, 6].length) (baseStart_4115872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4115872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4115872 prefixEnd_4115872 := by exact prefixLift 4115872
  have htrace : WordTrace (prefixWord ++ tailWord_4115872) baseStart_4115872 baseEnd_4115872 := by
    simpa [prefixWord, tailWord_4115872, baseEnd_4115872] using wordTrace_append hprefix tailTrace_4115872
  have hstable : (prefixWord ++ tailWord_4115872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4115872).length < 2 ^ (prefixWord ++ tailWord_4115872).sum := by decide
  have hdescent : baseEnd_4115872 < baseStart_4115872 := by decide
  rcases family_descends (prefixWord ++ tailWord_4115872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4115893 : List Nat := [1, 3, 3, 2, 2, 2, 2, 3, 1, 4]
def baseStart_4115893 : Nat := 118140960795 + 4115893 * 2 ^ 59
def prefixEnd_4115893 : Nat := 4983230072969 + 3 ^ 40 * 4115893 * 2
def baseEnd_4115893 : Nat := 704477143825323427802953

theorem tailTrace_4115893 : CollatzResearch.WordTrace tailWord_4115893 prefixEnd_4115893 704477143825323427802953 := by
  unfold tailWord_4115893
  simp only [CollatzResearch.WordTrace]
  refine ⟨150118950477830074405712333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100079300318553382937141555 150118950477830074405712333)
  ·
    refine ⟨56294606429186277902142125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 150118950477830074405712333 56294606429186277902142125)
    ·
      refine ⟨21110477410944854213303297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56294606429186277902142125 21110477410944854213303297)
      ·
        refine ⟨15832858058208640659977473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21110477410944854213303297 15832858058208640659977473)
        ·
          refine ⟨11874643543656480494983105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15832858058208640659977473 11874643543656480494983105)
          ·
            refine ⟨8905982657742360371237329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11874643543656480494983105 8905982657742360371237329)
            ·
              refine ⟨6679486993306770278427997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8905982657742360371237329 6679486993306770278427997)
              ·
                refine ⟨2504807622490038854410499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6679486993306770278427997 2504807622490038854410499)
                ·
                  refine ⟨3757211433735058281615749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2504807622490038854410499 3757211433735058281615749)
                  ·
                    refine ⟨704477143825323427802953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3757211433735058281615749 704477143825323427802953)
                    ·
                      rfl

theorem cell23_4115893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 2, 3, 1, 4].length) (baseStart_4115893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4115893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4115893 prefixEnd_4115893 := by exact prefixLift 4115893
  have htrace : WordTrace (prefixWord ++ tailWord_4115893) baseStart_4115893 baseEnd_4115893 := by
    simpa [prefixWord, tailWord_4115893, baseEnd_4115893] using wordTrace_append hprefix tailTrace_4115893
  have hstable : (prefixWord ++ tailWord_4115893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4115893).length < 2 ^ (prefixWord ++ tailWord_4115893).sum := by decide
  have hdescent : baseEnd_4115893 < baseStart_4115893 := by decide
  rcases family_descends (prefixWord ++ tailWord_4115893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4115916 : List Nat := [2, 2, 1, 4, 2, 1, 1, 3, 3, 1, 3]
def baseStart_4115916 : Nat := 118140960795 + 4115916 * 2 ^ 59
def prefixEnd_4115916 : Nat := 4983230072969 + 3 ^ 40 * 4115916 * 2
def baseEnd_4115916 : Nat := 2113443241531023693421253

theorem tailTrace_4115916 : CollatzResearch.WordTrace tailWord_4115916 prefixEnd_4115916 2113443241531023693421253 := by
  unfold tailWord_4115916
  simp only [CollatzResearch.WordTrace]
  refine ⟨75059894678373374666899801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100079859571164499555866401 75059894678373374666899801)
  ·
    refine ⟨56294921008780031000174851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75059894678373374666899801 56294921008780031000174851)
    ·
      refine ⟨84442381513170046500262277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56294921008780031000174851 84442381513170046500262277)
      ·
        refine ⟨15832946533719383718799177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 84442381513170046500262277 15832946533719383718799177)
        ·
          refine ⟨11874709900289537789099383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15832946533719383718799177 11874709900289537789099383)
          ·
            refine ⟨17812064850434306683649075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11874709900289537789099383 17812064850434306683649075)
            ·
              refine ⟨26718097275651460025473613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17812064850434306683649075 26718097275651460025473613)
              ·
                refine ⟨10019286478369297509552605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26718097275651460025473613 10019286478369297509552605)
                ·
                  refine ⟨3757232429388486566082227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10019286478369297509552605 3757232429388486566082227)
                  ·
                    refine ⟨5635848644082729849123341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3757232429388486566082227 5635848644082729849123341)
                    ·
                      refine ⟨2113443241531023693421253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5635848644082729849123341 2113443241531023693421253)
                      ·
                        rfl

theorem cell23_4115916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 1, 3, 3, 1, 3].length) (baseStart_4115916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4115916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4115916 prefixEnd_4115916 := by exact prefixLift 4115916
  have htrace : WordTrace (prefixWord ++ tailWord_4115916) baseStart_4115916 baseEnd_4115916 := by
    simpa [prefixWord, tailWord_4115916, baseEnd_4115916] using wordTrace_append hprefix tailTrace_4115916
  have hstable : (prefixWord ++ tailWord_4115916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4115916).length < 2 ^ (prefixWord ++ tailWord_4115916).sum := by decide
  have hdescent : baseEnd_4115916 < baseStart_4115916 := by decide
  rcases family_descends (prefixWord ++ tailWord_4115916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4115974 : List Nat := [6, 2, 1, 1, 3, 1, 2, 1, 6]
def baseStart_4115974 : Nat := 118140960795 + 4115974 * 2 ^ 59
def prefixEnd_4115974 : Nat := 4983230072969 + 3 ^ 40 * 4115974 * 2
def baseEnd_4115974 : Nat := 234830335934331607388443

theorem tailTrace_4115974 : CollatzResearch.WordTrace tailWord_4115974 prefixEnd_4115974 234830335934331607388443 := by
  unfold tailWord_4115974
  simp only [CollatzResearch.WordTrace]
  refine ⟨4691309524704269538731593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 100081269860357750159607317 4691309524704269538731593)
  ·
    refine ⟨3518482143528202154048695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4691309524704269538731593 3518482143528202154048695)
    ·
      refine ⟨5277723215292303231073043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3518482143528202154048695 5277723215292303231073043)
      ·
        refine ⟨7916584822938454846609565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5277723215292303231073043 7916584822938454846609565)
        ·
          refine ⟨2968719308601920567478587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7916584822938454846609565 2968719308601920567478587)
          ·
            refine ⟨4453078962902880851217881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2968719308601920567478587 4453078962902880851217881)
            ·
              refine ⟨3339809222177160638413411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4453078962902880851217881 3339809222177160638413411)
              ·
                refine ⟨5009713833265740957620117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3339809222177160638413411 5009713833265740957620117)
                ·
                  refine ⟨234830335934331607388443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5009713833265740957620117 234830335934331607388443)
                  ·
                    rfl

theorem cell23_4115974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 3, 1, 2, 1, 6].length) (baseStart_4115974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4115974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4115974 prefixEnd_4115974 := by exact prefixLift 4115974
  have htrace : WordTrace (prefixWord ++ tailWord_4115974) baseStart_4115974 baseEnd_4115974 := by
    simpa [prefixWord, tailWord_4115974, baseEnd_4115974] using wordTrace_append hprefix tailTrace_4115974
  have hstable : (prefixWord ++ tailWord_4115974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4115974).length < 2 ^ (prefixWord ++ tailWord_4115974).sum := by decide
  have hdescent : baseEnd_4115974 < baseStart_4115974 := by decide
  rcases family_descends (prefixWord ++ tailWord_4115974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4115979 : List Nat := [1, 1, 1, 1, 8, 1, 2, 8]
def baseStart_4115979 : Nat := 118140960795 + 4115979 * 2 ^ 59
def prefixEnd_4115979 : Nat := 4983230072969 + 3 ^ 40 * 4115979 * 2
def baseEnd_4115979 : Nat := 78276873733787294330869

theorem tailTrace_4115979 : CollatzResearch.WordTrace tailWord_4115979 prefixEnd_4115979 78276873733787294330869 := by
  unfold tailWord_4115979
  simp only [CollatzResearch.WordTrace]
  refine ⟨150122087155518511093342991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100081391437012340728895327 150122087155518511093342991)
  ·
    refine ⟨225183130733277766640014487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150122087155518511093342991 225183130733277766640014487)
    ·
      refine ⟨337774696099916649960021731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225183130733277766640014487 337774696099916649960021731)
      ·
        refine ⟨506662044149874974940032597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 337774696099916649960021731 506662044149874974940032597)
        ·
          refine ⟨5937445829881347362578507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 506662044149874974940032597 5937445829881347362578507)
          ·
            refine ⟨8906168744822021043867761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5937445829881347362578507 8906168744822021043867761)
            ·
              refine ⟨6679626558616515782900821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8906168744822021043867761 6679626558616515782900821)
              ·
                refine ⟨78276873733787294330869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6679626558616515782900821 78276873733787294330869)
                ·
                  rfl

theorem cell23_4115979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 2, 8].length) (baseStart_4115979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4115979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4115979 prefixEnd_4115979 := by exact prefixLift 4115979
  have htrace : WordTrace (prefixWord ++ tailWord_4115979) baseStart_4115979 baseEnd_4115979 := by
    simpa [prefixWord, tailWord_4115979, baseEnd_4115979] using wordTrace_append hprefix tailTrace_4115979
  have hstable : (prefixWord ++ tailWord_4115979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4115979).length < 2 ^ (prefixWord ++ tailWord_4115979).sum := by decide
  have hdescent : baseEnd_4115979 < baseStart_4115979 := by decide
  rcases family_descends (prefixWord ++ tailWord_4115979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4116023 : List Nat := [1, 1, 3, 1, 2, 5, 2, 2, 2, 1, 3]
def baseStart_4116023 : Nat := 118140960795 + 4116023 * 2 ^ 59
def prefixEnd_4116023 : Nat := 4983230072969 + 3 ^ 40 * 4116023 * 2
def baseEnd_4116023 : Nat := 2113498183961054774783261

theorem tailTrace_4116023 : CollatzResearch.WordTrace tailWord_4116023 prefixEnd_4116023 2113498183961054774783261 := by
  unfold tailWord_4116023
  simp only [CollatzResearch.WordTrace]
  refine ⟨150123691967359106607944723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100082461311572737738629815 150123691967359106607944723)
  ·
    refine ⟨225185537951038659911917085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150123691967359106607944723 225185537951038659911917085)
    ·
      refine ⟨84444576731639497466968907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 225185537951038659911917085 84444576731639497466968907)
      ·
        refine ⟨126666865097459246200453361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84444576731639497466968907 126666865097459246200453361)
        ·
          refine ⟨95000148823094434650340021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126666865097459246200453361 95000148823094434650340021)
          ·
            refine ⟨8906263952165103248469377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 95000148823094434650340021 8906263952165103248469377)
            ·
              refine ⟨6679697964123827436352033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8906263952165103248469377 6679697964123827436352033)
              ·
                refine ⟨5009773473092870577264025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6679697964123827436352033 5009773473092870577264025)
                ·
                  refine ⟨3757330104819652932948019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5009773473092870577264025 3757330104819652932948019)
                  ·
                    refine ⟨5635995157229479399422029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3757330104819652932948019 5635995157229479399422029)
                    ·
                      refine ⟨2113498183961054774783261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5635995157229479399422029 2113498183961054774783261)
                      ·
                        rfl

theorem cell23_4116023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 2, 2, 2, 1, 3].length) (baseStart_4116023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4116023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4116023 prefixEnd_4116023 := by exact prefixLift 4116023
  have htrace : WordTrace (prefixWord ++ tailWord_4116023) baseStart_4116023 baseEnd_4116023 := by
    simpa [prefixWord, tailWord_4116023, baseEnd_4116023] using wordTrace_append hprefix tailTrace_4116023
  have hstable : (prefixWord ++ tailWord_4116023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4116023).length < 2 ^ (prefixWord ++ tailWord_4116023).sum := by decide
  have hdescent : baseEnd_4116023 < baseStart_4116023 := by decide
  rcases family_descends (prefixWord ++ tailWord_4116023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4116049 : List Nat := [1, 2, 2, 1, 3, 2, 1, 2, 2, 4, 3]
def baseStart_4116049 : Nat := 118140960795 + 4116049 * 2 ^ 59
def prefixEnd_4116049 : Nat := 4983230072969 + 3 ^ 40 * 4116049 * 2
def baseEnd_4116049 : Nat := 2113511534458071673058141

theorem tailTrace_4116049 : CollatzResearch.WordTrace tailWord_4116049 prefixEnd_4116049 2113511534458071673058141 := by
  unfold tailWord_4116049
  simp only [CollatzResearch.WordTrace]
  refine ⟨150124640265264913048391201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100083093510176608698927467 150124640265264913048391201)
  ·
    refine ⟨112593480198948684786293401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150124640265264913048391201 112593480198948684786293401)
    ·
      refine ⟨84445110149211513589720051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112593480198948684786293401 84445110149211513589720051)
      ·
        refine ⟨126667665223817270384580077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84445110149211513589720051 126667665223817270384580077)
        ·
          refine ⟨47500374458931476394217529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 126667665223817270384580077 47500374458931476394217529)
          ·
            refine ⟨35625280844198607295663147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47500374458931476394217529 35625280844198607295663147)
            ·
              refine ⟨53437921266297910943494721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35625280844198607295663147 53437921266297910943494721)
              ·
                refine ⟨40078440949723433207621041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53437921266297910943494721 40078440949723433207621041)
                ·
                  refine ⟨30058830712292574905715781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40078440949723433207621041 30058830712292574905715781)
                  ·
                    refine ⟨5636030758554857794821709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30058830712292574905715781 5636030758554857794821709)
                    ·
                      refine ⟨2113511534458071673058141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5636030758554857794821709 2113511534458071673058141)
                      ·
                        rfl

theorem cell23_4116049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 2, 2, 4, 3].length) (baseStart_4116049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4116049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4116049 prefixEnd_4116049 := by exact prefixLift 4116049
  have htrace : WordTrace (prefixWord ++ tailWord_4116049) baseStart_4116049 baseEnd_4116049 := by
    simpa [prefixWord, tailWord_4116049, baseEnd_4116049] using wordTrace_append hprefix tailTrace_4116049
  have hstable : (prefixWord ++ tailWord_4116049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4116049).length < 2 ^ (prefixWord ++ tailWord_4116049).sum := by decide
  have hdescent : baseEnd_4116049 < baseStart_4116049 := by decide
  rcases family_descends (prefixWord ++ tailWord_4116049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4116080 : List Nat := [2, 1, 1, 1, 6, 1, 3, 2, 2, 2, 2]
def baseStart_4116080 : Nat := 118140960795 + 4116080 * 2 ^ 59
def prefixEnd_4116080 : Nat := 4983230072969 + 3 ^ 40 * 4116080 * 2
def baseEnd_4116080 : Nat := 2113527452358361051770499

theorem tailTrace_4116080 : CollatzResearch.WordTrace tailWord_4116080 prefixEnd_4116080 2113527452358361051770499 := by
  unfold tailWord_4116080
  simp only [CollatzResearch.WordTrace]
  refine ⟨75062885464076302671384847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100083847285435070228513129 75062885464076302671384847)
  ·
    refine ⟨112594328196114454007077271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75062885464076302671384847 112594328196114454007077271)
    ·
      refine ⟨168891492294171681010615907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112594328196114454007077271 168891492294171681010615907)
      ·
        refine ⟨253337238441257521515923861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168891492294171681010615907 253337238441257521515923861)
        ·
          refine ⟨11875183051933946321058931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 253337238441257521515923861 11875183051933946321058931)
          ·
            refine ⟨17812774577900919481588397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11875183051933946321058931 17812774577900919481588397)
            ·
              refine ⟨6679790466712844805595649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17812774577900919481588397 6679790466712844805595649)
              ·
                refine ⟨5009842850034633604196737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6679790466712844805595649 5009842850034633604196737)
                ·
                  refine ⟨3757382137525975203147553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5009842850034633604196737 3757382137525975203147553)
                  ·
                    refine ⟨2818036603144481402360665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3757382137525975203147553 2818036603144481402360665)
                    ·
                      refine ⟨2113527452358361051770499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2818036603144481402360665 2113527452358361051770499)
                      ·
                        rfl

theorem cell23_4116080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 3, 2, 2, 2, 2].length) (baseStart_4116080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4116080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4116080 prefixEnd_4116080 := by exact prefixLift 4116080
  have htrace : WordTrace (prefixWord ++ tailWord_4116080) baseStart_4116080 baseEnd_4116080 := by
    simpa [prefixWord, tailWord_4116080, baseEnd_4116080] using wordTrace_append hprefix tailTrace_4116080
  have hstable : (prefixWord ++ tailWord_4116080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4116080).length < 2 ^ (prefixWord ++ tailWord_4116080).sum := by decide
  have hdescent : baseEnd_4116080 < baseStart_4116080 := by decide
  rcases family_descends (prefixWord ++ tailWord_4116080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4116086 : List Nat := [5, 1, 1, 2, 2, 1, 1, 3, 7]
def baseStart_4116086 : Nat := 118140960795 + 4116086 * 2 ^ 59
def prefixEnd_4116086 : Nat := 4983230072969 + 3 ^ 40 * 4116086 * 2
def baseEnd_4116086 : Nat := 234836725915809780921719

theorem tailTrace_4116086 : CollatzResearch.WordTrace tailWord_4116086 prefixEnd_4116086 234836725915809780921719 := by
  unfold tailWord_4116086
  simp only [CollatzResearch.WordTrace]
  refine ⟨9382874360383179272968007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 100083993177420578911658741 9382874360383179272968007)
  ·
    refine ⟨14074311540574768909452011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9382874360383179272968007 14074311540574768909452011)
    ·
      refine ⟨21111467310862153364178017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14074311540574768909452011 21111467310862153364178017)
      ·
        refine ⟨15833600483146615023133513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21111467310862153364178017 15833600483146615023133513)
        ·
          refine ⟨11875200362359961267350135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15833600483146615023133513 11875200362359961267350135)
          ·
            refine ⟨17812800543539941901025203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11875200362359961267350135 17812800543539941901025203)
            ·
              refine ⟨26719200815309912851537805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17812800543539941901025203 26719200815309912851537805)
              ·
                refine ⟨10019700305741217319326677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26719200815309912851537805 10019700305741217319326677)
                ·
                  refine ⟨234836725915809780921719, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10019700305741217319326677 234836725915809780921719)
                  ·
                    rfl

theorem cell23_4116086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 1, 3, 7].length) (baseStart_4116086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4116086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4116086 prefixEnd_4116086 := by exact prefixLift 4116086
  have htrace : WordTrace (prefixWord ++ tailWord_4116086) baseStart_4116086 baseEnd_4116086 := by
    simpa [prefixWord, tailWord_4116086, baseEnd_4116086] using wordTrace_append hprefix tailTrace_4116086
  have hstable : (prefixWord ++ tailWord_4116086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4116086).length < 2 ^ (prefixWord ++ tailWord_4116086).sum := by decide
  have hdescent : baseEnd_4116086 < baseStart_4116086 := by decide
  rcases family_descends (prefixWord ++ tailWord_4116086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4116097 : List Nat := [1, 2, 4, 2, 1, 3, 3, 1, 2, 2, 2]
def baseStart_4116097 : Nat := 118140960795 + 4116097 * 2 ^ 59
def prefixEnd_4116097 : Nat := 4983230072969 + 3 ^ 40 * 4116097 * 2
def baseEnd_4116097 : Nat := 2113536181529487485257921

theorem tailTrace_4116097 : CollatzResearch.WordTrace tailWord_4116097 prefixEnd_4116097 2113536181529487485257921 := by
  unfold tailWord_4116097
  simp only [CollatzResearch.WordTrace]
  refine ⟨150126390969091017246138545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100084260646060678164092363 150126390969091017246138545)
  ·
    refine ⟨112594793226818262934603909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150126390969091017246138545 112594793226818262934603909)
    ·
      refine ⟨21111523730028424300238233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 112594793226818262934603909 21111523730028424300238233)
      ·
        refine ⟨15833642797521318225178675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21111523730028424300238233 15833642797521318225178675)
        ·
          refine ⟨23750464196281977337768013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15833642797521318225178675 23750464196281977337768013)
          ·
            refine ⟨8906424073605741501663005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23750464196281977337768013 8906424073605741501663005)
            ·
              refine ⟨3339909027602153063123627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8906424073605741501663005 3339909027602153063123627)
              ·
                refine ⟨5009863541403229594685441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3339909027602153063123627 5009863541403229594685441)
                ·
                  refine ⟨3757397656052422196014081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5009863541403229594685441 3757397656052422196014081)
                  ·
                    refine ⟨2818048242039316647010561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3757397656052422196014081 2818048242039316647010561)
                    ·
                      refine ⟨2113536181529487485257921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2818048242039316647010561 2113536181529487485257921)
                      ·
                        rfl

theorem cell23_4116097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 3, 1, 2, 2, 2].length) (baseStart_4116097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4116097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4116097 prefixEnd_4116097 := by exact prefixLift 4116097
  have htrace : WordTrace (prefixWord ++ tailWord_4116097) baseStart_4116097 baseEnd_4116097 := by
    simpa [prefixWord, tailWord_4116097, baseEnd_4116097] using wordTrace_append hprefix tailTrace_4116097
  have hstable : (prefixWord ++ tailWord_4116097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4116097).length < 2 ^ (prefixWord ++ tailWord_4116097).sum := by decide
  have hdescent : baseEnd_4116097 < baseStart_4116097 := by decide
  rcases family_descends (prefixWord ++ tailWord_4116097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4116139 : List Nat := [1, 1, 1, 1, 2, 1, 1, 1, 1, 10, 3]
def baseStart_4116139 : Nat := 118140960795 + 4116139 * 2 ^ 59
def prefixEnd_4116139 : Nat := 4983230072969 + 3 ^ 40 * 4116139 * 2
def baseEnd_4116139 : Nat := 2113557747716976320932727

theorem tailTrace_4116139 : CollatzResearch.WordTrace tailWord_4116139 prefixEnd_4116139 2113557747716976320932727 := by
  unfold tailWord_4116139
  simp only [CollatzResearch.WordTrace]
  refine ⟨150127922834938858419167471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100085281889959238946111647 150127922834938858419167471)
  ·
    refine ⟨225191884252408287628751207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150127922834938858419167471 225191884252408287628751207)
    ·
      refine ⟨337787826378612431443126811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225191884252408287628751207 337787826378612431443126811)
      ·
        refine ⟨506681739567918647164690217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 337787826378612431443126811 506681739567918647164690217)
        ·
          refine ⟨380011304675938985373517663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 506681739567918647164690217 380011304675938985373517663)
          ·
            refine ⟨570016957013908478060276495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 380011304675938985373517663 570016957013908478060276495)
            ·
              refine ⟨855025435520862717090414743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 570016957013908478060276495 855025435520862717090414743)
              ·
                refine ⟨1282538153281294075635622115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 855025435520862717090414743 1282538153281294075635622115)
                ·
                  refine ⟨1923807229921941113453433173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1282538153281294075635622115 1923807229921941113453433173)
                  ·
                    refine ⟨5636153993911936855820605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 1923807229921941113453433173 5636153993911936855820605)
                    ·
                      refine ⟨2113557747716976320932727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5636153993911936855820605 2113557747716976320932727)
                      ·
                        rfl

theorem cell23_4116139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 10, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 10, 3].length) (baseStart_4116139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4116139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4116139 prefixEnd_4116139 := by exact prefixLift 4116139
  have htrace : WordTrace (prefixWord ++ tailWord_4116139) baseStart_4116139 baseEnd_4116139 := by
    simpa [prefixWord, tailWord_4116139, baseEnd_4116139] using wordTrace_append hprefix tailTrace_4116139
  have hstable : (prefixWord ++ tailWord_4116139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4116139).length < 2 ^ (prefixWord ++ tailWord_4116139).sum := by decide
  have hdescent : baseEnd_4116139 < baseStart_4116139 := by decide
  rcases family_descends (prefixWord ++ tailWord_4116139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4116193 : List Nat := [1, 2, 3, 1, 5, 1, 2, 2, 6]
def baseStart_4116193 : Nat := 118140960795 + 4116193 * 2 ^ 59
def prefixEnd_4116193 : Nat := 4983230072969 + 3 ^ 40 * 4116193 * 2
def baseEnd_4116193 : Nat := 234842830630257678850831

theorem tailTrace_4116193 : CollatzResearch.WordTrace tailWord_4116193 prefixEnd_4116193 234842830630257678850831 := by
  unfold tailWord_4116193
  simp only [CollatzResearch.WordTrace]
  refine ⟨150129892376743225641633233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100086594917828817094422155 150129892376743225641633233)
  ·
    refine ⟨112597419282557419231224925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150129892376743225641633233 112597419282557419231224925)
    ·
      refine ⟨42224032230959032211709347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 112597419282557419231224925 42224032230959032211709347)
      ·
        refine ⟨63336048346438548317564021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42224032230959032211709347 63336048346438548317564021)
        ·
          refine ⟨5937754532478613904771627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 63336048346438548317564021 5937754532478613904771627)
          ·
            refine ⟨8906631798717920857157441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5937754532478613904771627 8906631798717920857157441)
            ·
              refine ⟨6679973849038440642868081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8906631798717920857157441 6679973849038440642868081)
              ·
                refine ⟨5009980386778830482151061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6679973849038440642868081 5009980386778830482151061)
                ·
                  refine ⟨234842830630257678850831, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5009980386778830482151061 234842830630257678850831)
                  ·
                    rfl

theorem cell23_4116193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 2, 2, 6].length) (baseStart_4116193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4116193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4116193 prefixEnd_4116193 := by exact prefixLift 4116193
  have htrace : WordTrace (prefixWord ++ tailWord_4116193) baseStart_4116193 baseEnd_4116193 := by
    simpa [prefixWord, tailWord_4116193, baseEnd_4116193] using wordTrace_append hprefix tailTrace_4116193
  have hstable : (prefixWord ++ tailWord_4116193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4116193).length < 2 ^ (prefixWord ++ tailWord_4116193).sum := by decide
  have hdescent : baseEnd_4116193 < baseStart_4116193 := by decide
  rcases family_descends (prefixWord ++ tailWord_4116193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4116206 : List Nat := [4, 1, 2, 1, 1, 2, 1, 1, 5, 5]
def baseStart_4116206 : Nat := 118140960795 + 4116206 * 2 ^ 59
def prefixEnd_4116206 : Nat := 4983230072969 + 3 ^ 40 * 4116206 * 2
def baseEnd_4116206 : Nat := 704530716973609186264973

theorem tailTrace_4116206 : CollatzResearch.WordTrace tailWord_4116206 prefixEnd_4116206 704530716973609186264973 := by
  unfold tailWord_4116206
  simp only [CollatzResearch.WordTrace]
  refine ⟨18766295815712016107732059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 100086911017130752574570981 18766295815712016107732059)
  ·
    refine ⟨28149443723568024161598089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18766295815712016107732059 28149443723568024161598089)
    ·
      refine ⟨21112082792676018121198567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28149443723568024161598089 21112082792676018121198567)
      ·
        refine ⟨31668124189014027181797851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21112082792676018121198567 31668124189014027181797851)
        ·
          refine ⟨47502186283521040772696777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31668124189014027181797851 47502186283521040772696777)
          ·
            refine ⟨35626639712640780579522583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47502186283521040772696777 35626639712640780579522583)
            ·
              refine ⟨53439959568961170869283875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35626639712640780579522583 53439959568961170869283875)
              ·
                refine ⟨80159939353441756303925813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53439959568961170869283875 80159939353441756303925813)
                ·
                  refine ⟨7514994314385164653493045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 80159939353441756303925813 7514994314385164653493045)
                  ·
                    refine ⟨704530716973609186264973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7514994314385164653493045 704530716973609186264973)
                    ·
                      rfl

theorem cell23_4116206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 1, 5, 5].length) (baseStart_4116206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4116206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4116206 prefixEnd_4116206 := by exact prefixLift 4116206
  have htrace : WordTrace (prefixWord ++ tailWord_4116206) baseStart_4116206 baseEnd_4116206 := by
    simpa [prefixWord, tailWord_4116206, baseEnd_4116206] using wordTrace_append hprefix tailTrace_4116206
  have hstable : (prefixWord ++ tailWord_4116206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4116206).length < 2 ^ (prefixWord ++ tailWord_4116206).sum := by decide
  have hdescent : baseEnd_4116206 < baseStart_4116206 := by decide
  rcases family_descends (prefixWord ++ tailWord_4116206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4116236 : List Nat := [2, 2, 1, 2, 2, 1, 4, 2, 1, 6]
def baseStart_4116236 : Nat := 118140960795 + 4116236 * 2 ^ 59
def prefixEnd_4116236 : Nat := 4983230072969 + 3 ^ 40 * 4116236 * 2
def baseEnd_4116236 : Nat := 704535851780154147139927

theorem tailTrace_4116236 : CollatzResearch.WordTrace tailWord_4116236 prefixEnd_4116236 704535851780154147139927 := by
  unfold tailWord_4116236
  simp only [CollatzResearch.WordTrace]
  refine ⟨75065730357793721992724281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100087640477058295990299041 75065730357793721992724281)
  ·
    refine ⟨56299297768345291494543211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75065730357793721992724281 56299297768345291494543211)
    ·
      refine ⟨84448946652517937241814817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56299297768345291494543211 84448946652517937241814817)
      ·
        refine ⟨63336709989388452931361113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84448946652517937241814817 63336709989388452931361113)
        ·
          refine ⟨47502532492041339698520835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63336709989388452931361113 47502532492041339698520835)
          ·
            refine ⟨71253798738062009547781253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47502532492041339698520835 71253798738062009547781253)
            ·
              refine ⟨13360087263386626790208985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 71253798738062009547781253 13360087263386626790208985)
              ·
                refine ⟨10020065447539970092656739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13360087263386626790208985 10020065447539970092656739)
                ·
                  refine ⟨15030098171309955138985109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10020065447539970092656739 15030098171309955138985109)
                  ·
                    refine ⟨704535851780154147139927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15030098171309955138985109 704535851780154147139927)
                    ·
                      rfl

theorem cell23_4116236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 4, 2, 1, 6].length) (baseStart_4116236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4116236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4116236 prefixEnd_4116236 := by exact prefixLift 4116236
  have htrace : WordTrace (prefixWord ++ tailWord_4116236) baseStart_4116236 baseEnd_4116236 := by
    simpa [prefixWord, tailWord_4116236, baseEnd_4116236] using wordTrace_append hprefix tailTrace_4116236
  have hstable : (prefixWord ++ tailWord_4116236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4116236).length < 2 ^ (prefixWord ++ tailWord_4116236).sum := by decide
  have hdescent : baseEnd_4116236 < baseStart_4116236 := by decide
  rcases family_descends (prefixWord ++ tailWord_4116236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4116244 : List Nat := [2, 4, 4, 1, 1, 2, 1, 2, 6]
def baseStart_4116244 : Nat := 118140960795 + 4116244 * 2 ^ 59
def prefixEnd_4116244 : Nat := 4983230072969 + 3 ^ 40 * 4116244 * 2
def baseEnd_4116244 : Nat := 234845740353966490013305

theorem tailTrace_4116244 : CollatzResearch.WordTrace tailWord_4116244 prefixEnd_4116244 234845740353966490013305 := by
  unfold tailWord_4116244
  simp only [CollatzResearch.WordTrace]
  refine ⟨75065876249779230675869893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100087834999705640901159857 75065876249779230675869893)
  ·
    refine ⟨14074851796833605751725605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 75065876249779230675869893 14074851796833605751725605)
    ·
      refine ⟨2639034711906301078448551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14074851796833605751725605 2639034711906301078448551)
      ·
        refine ⟨3958552067859451617672827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2639034711906301078448551 3958552067859451617672827)
        ·
          refine ⟨5937828101789177426509241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3958552067859451617672827 5937828101789177426509241)
          ·
            refine ⟨4453371076341883069881931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5937828101789177426509241 4453371076341883069881931)
            ·
              refine ⟨6680056614512824604822897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4453371076341883069881931 6680056614512824604822897)
              ·
                refine ⟨5010042460884618453617173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6680056614512824604822897 5010042460884618453617173)
                ·
                  refine ⟨234845740353966490013305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5010042460884618453617173 234845740353966490013305)
                  ·
                    rfl

theorem cell23_4116244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 2, 1, 2, 6].length) (baseStart_4116244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4116244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4116244 prefixEnd_4116244 := by exact prefixLift 4116244
  have htrace : WordTrace (prefixWord ++ tailWord_4116244) baseStart_4116244 baseEnd_4116244 := by
    simpa [prefixWord, tailWord_4116244, baseEnd_4116244] using wordTrace_append hprefix tailTrace_4116244
  have hstable : (prefixWord ++ tailWord_4116244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4116244).length < 2 ^ (prefixWord ++ tailWord_4116244).sum := by decide
  have hdescent : baseEnd_4116244 < baseStart_4116244 := by decide
  rcases family_descends (prefixWord ++ tailWord_4116244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4116256 : List Nat := [2, 1, 1, 5, 1, 1, 2, 2, 1, 1, 6]
def baseStart_4116256 : Nat := 118140960795 + 4116256 * 2 ^ 59
def prefixEnd_4116256 : Nat := 4983230072969 + 3 ^ 40 * 4116256 * 2
def baseEnd_4116256 : Nat := 2113617824953552363169689

theorem tailTrace_4116256 : CollatzResearch.WordTrace tailWord_4116256 prefixEnd_4116256 2113617824953552363169689 := by
  unfold tailWord_4116256
  simp only [CollatzResearch.WordTrace]
  refine ⟨75066095087757493700588311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100088126783676658267451081 75066095087757493700588311)
  ·
    refine ⟨112599142631636240550882467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75066095087757493700588311 112599142631636240550882467)
    ·
      refine ⟨168898713947454360826323701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112599142631636240550882467 168898713947454360826323701)
      ·
        refine ⟨15834254432573846327467847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 168898713947454360826323701 15834254432573846327467847)
        ·
          refine ⟨23751381648860769491201771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15834254432573846327467847 23751381648860769491201771)
          ·
            refine ⟨35627072473291154236802657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23751381648860769491201771 35627072473291154236802657)
            ·
              refine ⟨26720304354968365677601993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35627072473291154236802657 26720304354968365677601993)
              ·
                refine ⟨20040228266226274258201495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26720304354968365677601993 20040228266226274258201495)
                ·
                  refine ⟨30060342399339411387302243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20040228266226274258201495 30060342399339411387302243)
                  ·
                    refine ⟨45090513599009117080953365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30060342399339411387302243 45090513599009117080953365)
                    ·
                      refine ⟨2113617824953552363169689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 45090513599009117080953365 2113617824953552363169689)
                      ·
                        rfl

theorem cell23_4116256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 2, 2, 1, 1, 6].length) (baseStart_4116256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4116256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4116256 prefixEnd_4116256 := by exact prefixLift 4116256
  have htrace : WordTrace (prefixWord ++ tailWord_4116256) baseStart_4116256 baseEnd_4116256 := by
    simpa [prefixWord, tailWord_4116256, baseEnd_4116256] using wordTrace_append hprefix tailTrace_4116256
  have hstable : (prefixWord ++ tailWord_4116256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4116256).length < 2 ^ (prefixWord ++ tailWord_4116256).sum := by decide
  have hdescent : baseEnd_4116256 < baseStart_4116256 := by decide
  rcases family_descends (prefixWord ++ tailWord_4116256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4116273 : List Nat := [1, 2, 2, 3, 2, 2, 3, 1, 1, 2, 4]
def baseStart_4116273 : Nat := 118140960795 + 4116273 * 2 ^ 59
def prefixEnd_4116273 : Nat := 4983230072969 + 3 ^ 40 * 4116273 * 2
def baseEnd_4116273 : Nat := 2113626554124678796657111

theorem tailTrace_4116273 : CollatzResearch.WordTrace tailWord_4116273 prefixEnd_4116273 2113626554124678796657111 := by
  unfold tailWord_4116273
  simp only [CollatzResearch.WordTrace]
  refine ⟨150132810216453399304545473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100088540144302266203030315 150132810216453399304545473)
  ·
    refine ⟨112599607662340049478409105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150132810216453399304545473 112599607662340049478409105)
    ·
      refine ⟨84449705746755037108806829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112599607662340049478409105 84449705746755037108806829)
      ·
        refine ⟨31668639655033138915802561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84449705746755037108806829 31668639655033138915802561)
        ·
          refine ⟨23751479741274854186851921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31668639655033138915802561 23751479741274854186851921)
          ·
            refine ⟨17813609805956140640138941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23751479741274854186851921 17813609805956140640138941)
            ·
              refine ⟨6680103677233552740052103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17813609805956140640138941 6680103677233552740052103)
              ·
                refine ⟨10020155515850329110078155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6680103677233552740052103 10020155515850329110078155)
                ·
                  refine ⟨15030233273775493665117233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10020155515850329110078155 15030233273775493665117233)
                  ·
                    refine ⟨11272674955331620248837925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15030233273775493665117233 11272674955331620248837925)
                    ·
                      refine ⟨2113626554124678796657111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11272674955331620248837925 2113626554124678796657111)
                      ·
                        rfl

theorem cell23_4116273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 3, 1, 1, 2, 4].length) (baseStart_4116273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4116273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4116273 prefixEnd_4116273 := by exact prefixLift 4116273
  have htrace : WordTrace (prefixWord ++ tailWord_4116273) baseStart_4116273 baseEnd_4116273 := by
    simpa [prefixWord, tailWord_4116273, baseEnd_4116273] using wordTrace_append hprefix tailTrace_4116273
  have hstable : (prefixWord ++ tailWord_4116273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4116273).length < 2 ^ (prefixWord ++ tailWord_4116273).sum := by decide
  have hdescent : baseEnd_4116273 < baseStart_4116273 := by decide
  rcases family_descends (prefixWord ++ tailWord_4116273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4116280 : List Nat := [2, 1, 2, 1, 3, 4, 2, 2, 1, 2, 3]
def baseStart_4116280 : Nat := 118140960795 + 4116280 * 2 ^ 59
def prefixEnd_4116280 : Nat := 4983230072969 + 3 ^ 40 * 4116280 * 2
def baseEnd_4116280 : Nat := 2113630148489260269269579

theorem tailTrace_4116280 : CollatzResearch.WordTrace tailWord_4116280 prefixEnd_4116280 2113630148489260269269579 := by
  unfold tailWord_4116280
  simp only [CollatzResearch.WordTrace]
  refine ⟨75066532763714019750025147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100088710351618693000033529 75066532763714019750025147)
  ·
    refine ⟨112599799145571029625037721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75066532763714019750025147 112599799145571029625037721)
    ·
      refine ⟨84449849359178272218778291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112599799145571029625037721 84449849359178272218778291)
      ·
        refine ⟨126674774038767408328167437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84449849359178272218778291 126674774038767408328167437)
        ·
          refine ⟨47503040264537778123062789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 126674774038767408328167437 47503040264537778123062789)
          ·
            refine ⟨8906820049600833398074273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47503040264537778123062789 8906820049600833398074273)
            ·
              refine ⟨6680115037200625048555705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8906820049600833398074273 6680115037200625048555705)
              ·
                refine ⟨5010086277900468786416779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6680115037200625048555705 5010086277900468786416779)
                ·
                  refine ⟨7515129416850703179625169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5010086277900468786416779 7515129416850703179625169)
                  ·
                    refine ⟨5636347062638027384718877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7515129416850703179625169 5636347062638027384718877)
                    ·
                      refine ⟨2113630148489260269269579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5636347062638027384718877 2113630148489260269269579)
                      ·
                        rfl

theorem cell23_4116280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 2, 2, 1, 2, 3].length) (baseStart_4116280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4116280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4116280 prefixEnd_4116280 := by exact prefixLift 4116280
  have htrace : WordTrace (prefixWord ++ tailWord_4116280) baseStart_4116280 baseEnd_4116280 := by
    simpa [prefixWord, tailWord_4116280, baseEnd_4116280] using wordTrace_append hprefix tailTrace_4116280
  have hstable : (prefixWord ++ tailWord_4116280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4116280).length < 2 ^ (prefixWord ++ tailWord_4116280).sum := by decide
  have hdescent : baseEnd_4116280 < baseStart_4116280 := by decide
  rcases family_descends (prefixWord ++ tailWord_4116280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4116293 : List Nat := [1, 3, 1, 1, 1, 2, 3, 1, 6, 1, 3]
def baseStart_4116293 : Nat := 118140960795 + 4116293 * 2 ^ 59
def prefixEnd_4116293 : Nat := 4983230072969 + 3 ^ 40 * 4116293 * 2
def baseEnd_4116293 : Nat := 2113636823737768718407019

theorem tailTrace_4116293 : CollatzResearch.WordTrace tailWord_4116293 prefixEnd_4116293 2113636823737768718407019 := by
  unfold tailWord_4116293
  simp only [CollatzResearch.WordTrace]
  refine ⟨150133539676380942720273533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100089026450920628480182355 150133539676380942720273533)
  ·
    refine ⟨56300077378642853520102575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 150133539676380942720273533 56300077378642853520102575)
    ·
      refine ⟨84450116067964280280153863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56300077378642853520102575 84450116067964280280153863)
      ·
        refine ⟨126675174101946420420230795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84450116067964280280153863 126675174101946420420230795)
        ·
          refine ⟨190012761152919630630346193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126675174101946420420230795 190012761152919630630346193)
          ·
            refine ⟨142509570864689722972759645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 190012761152919630630346193 142509570864689722972759645)
            ·
              refine ⟨53441089074258646114784867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 142509570864689722972759645 53441089074258646114784867)
              ·
                refine ⟨80161633611387969172177301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53441089074258646114784867 80161633611387969172177301)
                ·
                  refine ⟨3757576575533811054945811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 80161633611387969172177301 3757576575533811054945811)
                  ·
                    refine ⟨5636364863300716582418717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3757576575533811054945811 5636364863300716582418717)
                    ·
                      refine ⟨2113636823737768718407019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5636364863300716582418717 2113636823737768718407019)
                      ·
                        rfl

theorem cell23_4116293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 1, 6, 1, 3].length) (baseStart_4116293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4116293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4116293 prefixEnd_4116293 := by exact prefixLift 4116293
  have htrace : WordTrace (prefixWord ++ tailWord_4116293) baseStart_4116293 baseEnd_4116293 := by
    simpa [prefixWord, tailWord_4116293, baseEnd_4116293] using wordTrace_append hprefix tailTrace_4116293
  have hstable : (prefixWord ++ tailWord_4116293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4116293).length < 2 ^ (prefixWord ++ tailWord_4116293).sum := by decide
  have hdescent : baseEnd_4116293 < baseStart_4116293 := by decide
  rcases family_descends (prefixWord ++ tailWord_4116293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4116311 : List Nat := [1, 1, 3, 2, 5, 1, 3, 2, 1, 2, 2]
def baseStart_4116311 : Nat := 118140960795 + 4116311 * 2 ^ 59
def prefixEnd_4116311 : Nat := 4983230072969 + 3 ^ 40 * 4116311 * 2
def baseEnd_4116311 : Nat := 2113646066389549647981937

theorem tailTrace_4116311 : CollatzResearch.WordTrace tailWord_4116311 prefixEnd_4116311 2113646066389549647981937 := by
  unfold tailWord_4116311
  simp only [CollatzResearch.WordTrace]
  refine ⟨150134196190315731794428787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100089464126877154529619191 150134196190315731794428787)
  ·
    refine ⟨225201294285473597691643181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150134196190315731794428787 225201294285473597691643181)
    ·
      refine ⟨84450485357052599134366193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 225201294285473597691643181 84450485357052599134366193)
      ·
        refine ⟨63337864017789449350774645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84450485357052599134366193 63337864017789449350774645)
        ·
          refine ⟨5937924751667760876635123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 63337864017789449350774645 5937924751667760876635123)
          ·
            refine ⟨8906887127501641314952685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5937924751667760876635123 8906887127501641314952685)
            ·
              refine ⟨3340082672813115493107257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8906887127501641314952685 3340082672813115493107257)
              ·
                refine ⟨2505062004609836619830443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3340082672813115493107257 2505062004609836619830443)
                ·
                  refine ⟨3757593006914754929745665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2505062004609836619830443 3757593006914754929745665)
                  ·
                    refine ⟨2818194755186066197309249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3757593006914754929745665 2818194755186066197309249)
                    ·
                      refine ⟨2113646066389549647981937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2818194755186066197309249 2113646066389549647981937)
                      ·
                        rfl

theorem cell23_4116311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 3, 2, 1, 2, 2].length) (baseStart_4116311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4116311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4116311 prefixEnd_4116311 := by exact prefixLift 4116311
  have htrace : WordTrace (prefixWord ++ tailWord_4116311) baseStart_4116311 baseEnd_4116311 := by
    simpa [prefixWord, tailWord_4116311, baseEnd_4116311] using wordTrace_append hprefix tailTrace_4116311
  have hstable : (prefixWord ++ tailWord_4116311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4116311).length < 2 ^ (prefixWord ++ tailWord_4116311).sum := by decide
  have hdescent : baseEnd_4116311 < baseStart_4116311 := by decide
  rcases family_descends (prefixWord ++ tailWord_4116311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4116370 : List Nat := [3, 2, 3, 2, 1, 1, 1, 1, 2, 4, 3]
def baseStart_4116370 : Nat := 118140960795 + 4116370 * 2 ^ 59
def prefixEnd_4116370 : Nat := 4983230072969 + 3 ^ 40 * 4116370 * 2
def baseEnd_4116370 : Nat := 2113676361748164917144165

theorem tailTrace_4116370 : CollatzResearch.WordTrace tailWord_4116370 prefixEnd_4116370 2113676361748164917144165 := by
  unfold tailWord_4116370
  simp only [CollatzResearch.WordTrace]
  refine ⟨37534087024275496217706641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100090898731401323247217709 37534087024275496217706641)
  ·
    refine ⟨28150565268206622163279981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37534087024275496217706641 28150565268206622163279981)
    ·
      refine ⟨10556461975577483311229993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28150565268206622163279981 10556461975577483311229993)
      ·
        refine ⟨7917346481683112483422495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10556461975577483311229993 7917346481683112483422495)
        ·
          refine ⟨11876019722524668725133743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7917346481683112483422495 11876019722524668725133743)
          ·
            refine ⟨17814029583787003087700615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11876019722524668725133743 17814029583787003087700615)
            ·
              refine ⟨26721044375680504631550923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17814029583787003087700615 26721044375680504631550923)
              ·
                refine ⟨40081566563520756947326385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26721044375680504631550923 40081566563520756947326385)
                ·
                  refine ⟨30061174922640567710494789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40081566563520756947326385 30061174922640567710494789)
                  ·
                    refine ⟨5636470297995106445717773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30061174922640567710494789 5636470297995106445717773)
                    ·
                      refine ⟨2113676361748164917144165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5636470297995106445717773 2113676361748164917144165)
                      ·
                        rfl

theorem cell23_4116370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 1, 1, 2, 4, 3].length) (baseStart_4116370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4116370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4116370 prefixEnd_4116370 := by exact prefixLift 4116370
  have htrace : WordTrace (prefixWord ++ tailWord_4116370) baseStart_4116370 baseEnd_4116370 := by
    simpa [prefixWord, tailWord_4116370, baseEnd_4116370] using wordTrace_append hprefix tailTrace_4116370
  have hstable : (prefixWord ++ tailWord_4116370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4116370).length < 2 ^ (prefixWord ++ tailWord_4116370).sum := by decide
  have hdescent : baseEnd_4116370 < baseStart_4116370 := by decide
  rcases family_descends (prefixWord ++ tailWord_4116370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4116380 : List Nat := [2, 2, 3, 3, 1, 2, 1, 1, 2, 2, 4]
def baseStart_4116380 : Nat := 118140960795 + 4116380 * 2 ^ 59
def prefixEnd_4116380 : Nat := 4983230072969 + 3 ^ 40 * 4116380 * 2
def baseEnd_4116380 : Nat := 2113681496554709878019119

theorem tailTrace_4116380 : CollatzResearch.WordTrace tailWord_4116380 prefixEnd_4116380 2113681496554709878019119 := by
  unfold tailWord_4116380
  simp only [CollatzResearch.WordTrace]
  refine ⟨75068356413532878289345297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100091141884710504385793729 75068356413532878289345297)
  ·
    refine ⟨56301267310149658717008973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75068356413532878289345297 56301267310149658717008973)
    ·
      refine ⟨21112975241306122018878365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56301267310149658717008973 21112975241306122018878365)
      ·
        refine ⟨7917365715489795757079387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21112975241306122018878365 7917365715489795757079387)
        ·
          refine ⟨11876048573234693635619081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7917365715489795757079387 11876048573234693635619081)
          ·
            refine ⟨8907036429926020226714311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11876048573234693635619081 8907036429926020226714311)
            ·
              refine ⟨13360554644889030340071467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8907036429926020226714311 13360554644889030340071467)
              ·
                refine ⟨20040831967333545510107201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13360554644889030340071467 20040831967333545510107201)
                ·
                  refine ⟨15030623975500159132580401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20040831967333545510107201 15030623975500159132580401)
                  ·
                    refine ⟨11272967981625119349435301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15030623975500159132580401 11272967981625119349435301)
                    ·
                      refine ⟨2113681496554709878019119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11272967981625119349435301 2113681496554709878019119)
                      ·
                        rfl

theorem cell23_4116380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 1, 1, 2, 2, 4].length) (baseStart_4116380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4116380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4116380 prefixEnd_4116380 := by exact prefixLift 4116380
  have htrace : WordTrace (prefixWord ++ tailWord_4116380) baseStart_4116380 baseEnd_4116380 := by
    simpa [prefixWord, tailWord_4116380, baseEnd_4116380] using wordTrace_append hprefix tailTrace_4116380
  have hstable : (prefixWord ++ tailWord_4116380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4116380).length < 2 ^ (prefixWord ++ tailWord_4116380).sum := by decide
  have hdescent : baseEnd_4116380 < baseStart_4116380 := by decide
  rcases family_descends (prefixWord ++ tailWord_4116380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4116423 : List Nat := [1, 1, 4, 1, 1, 2, 1, 3, 4, 1, 4]
def baseStart_4116423 : Nat := 118140960795 + 4116423 * 2 ^ 59
def prefixEnd_4116423 : Nat := 4983230072969 + 3 ^ 40 * 4116423 * 2
def baseEnd_4116423 : Nat := 2113703576222853209781421

theorem tailTrace_4116423 : CollatzResearch.WordTrace tailWord_4116423 prefixEnd_4116423 2113703576222853209781421 := by
  unfold tailWord_4116423
  simp only [CollatzResearch.WordTrace]
  refine ⟨150138281165909974922505923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100092187443939983281670615 150138281165909974922505923)
  ·
    refine ⟨225207421748864962383758885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150138281165909974922505923 225207421748864962383758885)
    ·
      refine ⟨42226391577912180446954791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 225207421748864962383758885 42226391577912180446954791)
      ·
        refine ⟨63339587366868270670432187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42226391577912180446954791 63339587366868270670432187)
        ·
          refine ⟨95009381050302406005648281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63339587366868270670432187 95009381050302406005648281)
          ·
            refine ⟨71257035787726804504236211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95009381050302406005648281 71257035787726804504236211)
            ·
              refine ⟨106885553681590206756354317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71257035787726804504236211 106885553681590206756354317)
              ·
                refine ⟨40082082630596327533632869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 106885553681590206756354317 40082082630596327533632869)
                ·
                  refine ⟨7515390493236811412556163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40082082630596327533632869 7515390493236811412556163)
                  ·
                    refine ⟨11273085739855217118834245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7515390493236811412556163 11273085739855217118834245)
                    ·
                      refine ⟨2113703576222853209781421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11273085739855217118834245 2113703576222853209781421)
                      ·
                        rfl

theorem cell23_4116423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 3, 4, 1, 4].length) (baseStart_4116423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4116423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4116423 prefixEnd_4116423 := by exact prefixLift 4116423
  have htrace : WordTrace (prefixWord ++ tailWord_4116423) baseStart_4116423 baseEnd_4116423 := by
    simpa [prefixWord, tailWord_4116423, baseEnd_4116423] using wordTrace_append hprefix tailTrace_4116423
  have hstable : (prefixWord ++ tailWord_4116423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4116423).length < 2 ^ (prefixWord ++ tailWord_4116423).sum := by decide
  have hdescent : baseEnd_4116423 < baseStart_4116423 := by decide
  rcases family_descends (prefixWord ++ tailWord_4116423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4116440 : List Nat := [2, 1, 2, 2, 2, 2, 1, 3, 2, 4, 2]
def baseStart_4116440 : Nat := 118140960795 + 4116440 * 2 ^ 59
def prefixEnd_4116440 : Nat := 4983230072969 + 3 ^ 40 * 4116440 * 2
def baseEnd_4116440 : Nat := 2113712305393979643268843

theorem tailTrace_4116440 : CollatzResearch.WordTrace tailWord_4116440 prefixEnd_4116440 2113712305393979643268843 := by
  unfold tailWord_4116440
  simp only [CollatzResearch.WordTrace]
  refine ⟨75069450603424193412937387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100092600804565591217249849 75069450603424193412937387)
  ·
    refine ⟨112604175905136290119406081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75069450603424193412937387 112604175905136290119406081)
    ·
      refine ⟨84453131928852217589554561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112604175905136290119406081 84453131928852217589554561)
      ·
        refine ⟨63339848946639163192165921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84453131928852217589554561 63339848946639163192165921)
        ·
          refine ⟨47504886709979372394124441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63339848946639163192165921 47504886709979372394124441)
          ·
            refine ⟨35628665032484529295593331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47504886709979372394124441 35628665032484529295593331)
            ·
              refine ⟨53442997548726793943389997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35628665032484529295593331 53442997548726793943389997)
              ·
                refine ⟨20041124080772547728771249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53442997548726793943389997 20041124080772547728771249)
                ·
                  refine ⟨15030843060579410796578437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20041124080772547728771249 15030843060579410796578437)
                  ·
                    refine ⟨2818283073858639524358457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15030843060579410796578437 2818283073858639524358457)
                    ·
                      refine ⟨2113712305393979643268843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2818283073858639524358457 2113712305393979643268843)
                      ·
                        rfl

theorem cell23_4116440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 3, 2, 4, 2].length) (baseStart_4116440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4116440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4116440 prefixEnd_4116440 := by exact prefixLift 4116440
  have htrace : WordTrace (prefixWord ++ tailWord_4116440) baseStart_4116440 baseEnd_4116440 := by
    simpa [prefixWord, tailWord_4116440, baseEnd_4116440] using wordTrace_append hprefix tailTrace_4116440
  have hstable : (prefixWord ++ tailWord_4116440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4116440).length < 2 ^ (prefixWord ++ tailWord_4116440).sum := by decide
  have hdescent : baseEnd_4116440 < baseStart_4116440 := by decide
  rcases family_descends (prefixWord ++ tailWord_4116440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4116517 : List Nat := [1, 3, 1, 2, 2, 3, 1, 3, 2, 3, 2]
def baseStart_4116517 : Nat := 118140960795 + 4116517 * 2 ^ 59
def prefixEnd_4116517 : Nat := 4983230072969 + 3 ^ 40 * 4116517 * 2
def baseEnd_4116517 : Nat := 2113751843404375842005989

theorem tailTrace_4116517 : CollatzResearch.WordTrace tailWord_4116517 prefixEnd_4116517 2113751843404375842005989 := by
  unfold tailWord_4116517
  simp only [CollatzResearch.WordTrace]
  refine ⟨150141709627569428976427805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100094473085046285984285203 150141709627569428976427805)
  ·
    refine ⟨56303141110338535866160427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 150141709627569428976427805 56303141110338535866160427)
    ·
      refine ⟨84454711665507803799240641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56303141110338535866160427 84454711665507803799240641)
      ·
        refine ⟨63341033749130852849430481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84454711665507803799240641 63341033749130852849430481)
        ·
          refine ⟨47505775311848139637072861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63341033749130852849430481 47505775311848139637072861)
          ·
            refine ⟨17814665741943052363902323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47505775311848139637072861 17814665741943052363902323)
            ·
              refine ⟨26721998612914578545853485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17814665741943052363902323 26721998612914578545853485)
              ·
                refine ⟨10020749479842966954695057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26721998612914578545853485 10020749479842966954695057)
                ·
                  refine ⟨7515562109882225216021293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10020749479842966954695057 7515562109882225216021293)
                  ·
                    refine ⟨2818335791205834456007985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7515562109882225216021293 2818335791205834456007985)
                    ·
                      refine ⟨2113751843404375842005989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2818335791205834456007985 2113751843404375842005989)
                      ·
                        rfl

theorem cell23_4116517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 1, 3, 2, 3, 2].length) (baseStart_4116517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4116517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4116517 prefixEnd_4116517 := by exact prefixLift 4116517
  have htrace : WordTrace (prefixWord ++ tailWord_4116517) baseStart_4116517 baseEnd_4116517 := by
    simpa [prefixWord, tailWord_4116517, baseEnd_4116517] using wordTrace_append hprefix tailTrace_4116517
  have hstable : (prefixWord ++ tailWord_4116517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4116517).length < 2 ^ (prefixWord ++ tailWord_4116517).sum := by decide
  have hdescent : baseEnd_4116517 < baseStart_4116517 := by decide
  rcases family_descends (prefixWord ++ tailWord_4116517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4116534 : List Nat := [5, 1, 2, 1, 1, 1, 1, 4, 2, 3, 2]
def baseStart_4116534 : Nat := 118140960795 + 4116534 * 2 ^ 59
def prefixEnd_4116534 : Nat := 4983230072969 + 3 ^ 40 * 4116534 * 2
def baseEnd_4116534 : Nat := 2113760572575502275493411

theorem tailTrace_4116534 : CollatzResearch.WordTrace tailWord_4116534 prefixEnd_4116534 2113760572575502275493411 := by
  unfold tailWord_4116534
  simp only [CollatzResearch.WordTrace]
  refine ⟨9383895604281740054987291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 100094886445671893919864437 9383895604281740054987291)
  ·
    refine ⟨14075843406422610082480937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9383895604281740054987291 14075843406422610082480937)
    ·
      refine ⟨10556882554816957561860703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14075843406422610082480937 10556882554816957561860703)
      ·
        refine ⟨15835323832225436342791055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10556882554816957561860703 15835323832225436342791055)
        ·
          refine ⟨23752985748338154514186583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15835323832225436342791055 23752985748338154514186583)
          ·
            refine ⟨35629478622507231771279875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23752985748338154514186583 35629478622507231771279875)
            ·
              refine ⟨53444217933760847656919813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35629478622507231771279875 53444217933760847656919813)
              ·
                refine ⟨10020790862580158935672465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53444217933760847656919813 10020790862580158935672465)
                ·
                  refine ⟨7515593146935119201754349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10020790862580158935672465 7515593146935119201754349)
                  ·
                    refine ⟨2818347430100669700657881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7515593146935119201754349 2818347430100669700657881)
                    ·
                      refine ⟨2113760572575502275493411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2818347430100669700657881 2113760572575502275493411)
                      ·
                        rfl

theorem cell23_4116534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 4, 2, 3, 2].length) (baseStart_4116534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4116534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4116534 prefixEnd_4116534 := by exact prefixLift 4116534
  have htrace : WordTrace (prefixWord ++ tailWord_4116534) baseStart_4116534 baseEnd_4116534 := by
    simpa [prefixWord, tailWord_4116534, baseEnd_4116534] using wordTrace_append hprefix tailTrace_4116534
  have hstable : (prefixWord ++ tailWord_4116534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4116534).length < 2 ^ (prefixWord ++ tailWord_4116534).sum := by decide
  have hdescent : baseEnd_4116534 < baseStart_4116534 := by decide
  rcases family_descends (prefixWord ++ tailWord_4116534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4116543 : List Nat := [1, 1, 2, 2, 3, 1, 2, 1, 3, 1, 6]
def baseStart_4116543 : Nat := 118140960795 + 4116543 * 2 ^ 59
def prefixEnd_4116543 : Nat := 4983230072969 + 3 ^ 40 * 4116543 * 2
def baseEnd_4116543 : Nat := 2113765193901392740280869

theorem tailTrace_4116543 : CollatzResearch.WordTrace tailWord_4116543 prefixEnd_4116543 2113765193901392740280869 := by
  unfold tailWord_4116543
  simp only [CollatzResearch.WordTrace]
  refine ⟨150142657925475235416874283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100095105283650156944582855 150142657925475235416874283)
  ·
    refine ⟨225213986888212853125311425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150142657925475235416874283 225213986888212853125311425)
    ·
      refine ⟨168910490166159639843983569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 225213986888212853125311425 168910490166159639843983569)
      ·
        refine ⟨126682867624619729882987677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 168910490166159639843983569 126682867624619729882987677)
        ·
          refine ⟨47506075359232398706120379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 126682867624619729882987677 47506075359232398706120379)
          ·
            refine ⟨71259113038848598059180569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47506075359232398706120379 71259113038848598059180569)
            ·
              refine ⟨53444334779136448544385427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71259113038848598059180569 53444334779136448544385427)
              ·
                refine ⟨80166502168704672816578141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53444334779136448544385427 80166502168704672816578141)
                ·
                  refine ⟨30062438313264252306216803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 80166502168704672816578141 30062438313264252306216803)
                  ·
                    refine ⟨45093657469896378459325205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30062438313264252306216803 45093657469896378459325205)
                    ·
                      refine ⟨2113765193901392740280869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 45093657469896378459325205 2113765193901392740280869)
                      ·
                        rfl

theorem cell23_4116543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 1, 3, 1, 6].length) (baseStart_4116543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4116543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4116543 prefixEnd_4116543 := by exact prefixLift 4116543
  have htrace : WordTrace (prefixWord ++ tailWord_4116543) baseStart_4116543 baseEnd_4116543 := by
    simpa [prefixWord, tailWord_4116543, baseEnd_4116543] using wordTrace_append hprefix tailTrace_4116543
  have hstable : (prefixWord ++ tailWord_4116543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4116543).length < 2 ^ (prefixWord ++ tailWord_4116543).sum := by decide
  have hdescent : baseEnd_4116543 < baseStart_4116543 := by decide
  rcases family_descends (prefixWord ++ tailWord_4116543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4116557 : List Nat := [1, 6, 1, 1, 1, 1, 4, 1, 1, 6]
def baseStart_4116557 : Nat := 118140960795 + 4116557 * 2 ^ 59
def prefixEnd_4116557 : Nat := 4983230072969 + 3 ^ 40 * 4116557 * 2
def baseEnd_4116557 : Nat := 704590794210185228501935

theorem tailTrace_4116557 : CollatzResearch.WordTrace tailWord_4116557 prefixEnd_4116557 704590794210185228501935 := by
  unfold tailWord_4116557
  simp only [CollatzResearch.WordTrace]
  refine ⟨150143168547424515807883925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100095445698283010538589283 150143168547424515807883925)
  ·
    refine ⟨7037961025660524178494559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 150143168547424515807883925 7037961025660524178494559)
    ·
      refine ⟨10556941538490786267741839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7037961025660524178494559 10556941538490786267741839)
      ·
        refine ⟨15835412307736179401612759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10556941538490786267741839 15835412307736179401612759)
        ·
          refine ⟨23753118461604269102419139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15835412307736179401612759 23753118461604269102419139)
          ·
            refine ⟨35629677692406403653628709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23753118461604269102419139 35629677692406403653628709)
            ·
              refine ⟨6680564567326200685055383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35629677692406403653628709 6680564567326200685055383)
              ·
                refine ⟨10020846850989301027583075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6680564567326200685055383 10020846850989301027583075)
                ·
                  refine ⟨15031270276483951541374613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10020846850989301027583075 15031270276483951541374613)
                  ·
                    refine ⟨704590794210185228501935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15031270276483951541374613 704590794210185228501935)
                    ·
                      rfl

theorem cell23_4116557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 4, 1, 1, 6].length) (baseStart_4116557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4116557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4116557 prefixEnd_4116557 := by exact prefixLift 4116557
  have htrace : WordTrace (prefixWord ++ tailWord_4116557) baseStart_4116557 baseEnd_4116557 := by
    simpa [prefixWord, tailWord_4116557, baseEnd_4116557] using wordTrace_append hprefix tailTrace_4116557
  have hstable : (prefixWord ++ tailWord_4116557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4116557).length < 2 ^ (prefixWord ++ tailWord_4116557).sum := by decide
  have hdescent : baseEnd_4116557 < baseStart_4116557 := by decide
  rcases family_descends (prefixWord ++ tailWord_4116557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4116570 : List Nat := [3, 1, 1, 2, 1, 1, 7, 7]
def baseStart_4116570 : Nat := 118140960795 + 4116570 * 2 ^ 59
def prefixEnd_4116570 : Nat := 4983230072969 + 3 ^ 40 * 4116570 * 2
def baseEnd_4116570 : Nat := 78288113254780153134935

theorem tailTrace_4116570 : CollatzResearch.WordTrace tailWord_4116570 prefixEnd_4116570 78288113254780153134935 := by
  unfold tailWord_4116570
  simp only [CollatzResearch.WordTrace]
  refine ⟨37535910674094354757026791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100095761797584946018738109 37535910674094354757026791)
  ·
    refine ⟨56303866011141532135540187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37535910674094354757026791 56303866011141532135540187)
    ·
      refine ⟨84455799016712298203310281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56303866011141532135540187 84455799016712298203310281)
      ·
        refine ⟨63341849262534223652482711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84455799016712298203310281 63341849262534223652482711)
        ·
          refine ⟨95012773893801335478724067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63341849262534223652482711 95012773893801335478724067)
          ·
            refine ⟨142519160840702003218086101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95012773893801335478724067 142519160840702003218086101)
            ·
              refine ⟨3340292832203953200423893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 142519160840702003218086101 3340292832203953200423893)
              ·
                refine ⟨78288113254780153134935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3340292832203953200423893 78288113254780153134935)
                ·
                  rfl

theorem cell23_4116570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 7, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 7, 7].length) (baseStart_4116570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4116570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4116570 prefixEnd_4116570 := by exact prefixLift 4116570
  have htrace : WordTrace (prefixWord ++ tailWord_4116570) baseStart_4116570 baseEnd_4116570 := by
    simpa [prefixWord, tailWord_4116570, baseEnd_4116570] using wordTrace_append hprefix tailTrace_4116570
  have hstable : (prefixWord ++ tailWord_4116570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4116570).length < 2 ^ (prefixWord ++ tailWord_4116570).sum := by decide
  have hdescent : baseEnd_4116570 < baseStart_4116570 := by decide
  rcases family_descends (prefixWord ++ tailWord_4116570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4116578 : List Nat := [3, 3, 2, 2, 3, 1, 2, 1, 1, 5]
def baseStart_4116578 : Nat := 118140960795 + 4116578 * 2 ^ 59
def prefixEnd_4116578 : Nat := 4983230072969 + 3 ^ 40 * 4116578 * 2
def baseEnd_4116578 : Nat := 704594388574766701114403

theorem tailTrace_4116578 : CollatzResearch.WordTrace tailWord_4116578 prefixEnd_4116578 704594388574766701114403 := by
  unfold tailWord_4116578
  simp only [CollatzResearch.WordTrace]
  refine ⟨37535983620087109098599597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100095956320232290929598925 37535983620087109098599597)
  ·
    refine ⟨14075993857532665911974849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37535983620087109098599597 14075993857532665911974849)
    ·
      refine ⟨10556995393149499433981137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14075993857532665911974849 10556995393149499433981137)
      ·
        refine ⟨7917746544862124575485853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10556995393149499433981137 7917746544862124575485853)
        ·
          refine ⟨2969154954323296715807195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7917746544862124575485853 2969154954323296715807195)
          ·
            refine ⟨4453732431484945073710793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2969154954323296715807195 4453732431484945073710793)
            ·
              refine ⟨3340299323613708805283095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4453732431484945073710793 3340299323613708805283095)
              ·
                refine ⟨5010448985420563207924643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3340299323613708805283095 5010448985420563207924643)
                ·
                  refine ⟨7515673478130844811886965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5010448985420563207924643 7515673478130844811886965)
                  ·
                    refine ⟨704594388574766701114403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7515673478130844811886965 704594388574766701114403)
                    ·
                      rfl

theorem cell23_4116578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 3, 1, 2, 1, 1, 5].length) (baseStart_4116578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4116578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4116578 prefixEnd_4116578 := by exact prefixLift 4116578
  have htrace : WordTrace (prefixWord ++ tailWord_4116578) baseStart_4116578 baseEnd_4116578 := by
    simpa [prefixWord, tailWord_4116578, baseEnd_4116578] using wordTrace_append hprefix tailTrace_4116578
  have hstable : (prefixWord ++ tailWord_4116578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4116578).length < 2 ^ (prefixWord ++ tailWord_4116578).sum := by decide
  have hdescent : baseEnd_4116578 < baseStart_4116578 := by decide
  rcases family_descends (prefixWord ++ tailWord_4116578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4116581 : List Nat := [1, 3, 1, 3, 2, 2, 1, 5, 1, 2, 2]
def baseStart_4116581 : Nat := 118140960795 + 4116581 * 2 ^ 59
def prefixEnd_4116581 : Nat := 4983230072969 + 3 ^ 40 * 4116581 * 2
def baseEnd_4116581 : Nat := 2113784706166263591605695

theorem tailTrace_4116581 : CollatzResearch.WordTrace tailWord_4116581 prefixEnd_4116581 2113784706166263591605695 := by
  unfold tailWord_4116581
  simp only [CollatzResearch.WordTrace]
  refine ⟨150144043899337567906757597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100096029266225045271171731 150144043899337567906757597)
  ·
    refine ⟨56304016462251587965034099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 150144043899337567906757597 56304016462251587965034099)
    ·
      refine ⟨84456024693377381947551149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56304016462251587965034099 84456024693377381947551149)
      ·
        refine ⟨31671009260016518230331681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84456024693377381947551149 31671009260016518230331681)
        ·
          refine ⟨23753256945012388672748761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31671009260016518230331681 23753256945012388672748761)
          ·
            refine ⟨17814942708759291504561571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23753256945012388672748761 17814942708759291504561571)
            ·
              refine ⟨26722414063138937256842357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17814942708759291504561571 26722414063138937256842357)
              ·
                refine ⟨2505226318419275367828971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26722414063138937256842357 2505226318419275367828971)
                ·
                  refine ⟨3757839477628913051743457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2505226318419275367828971 3757839477628913051743457)
                  ·
                    refine ⟨2818379608221684788807593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3757839477628913051743457 2818379608221684788807593)
                    ·
                      refine ⟨2113784706166263591605695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2818379608221684788807593 2113784706166263591605695)
                      ·
                        rfl

theorem cell23_4116581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 1, 5, 1, 2, 2].length) (baseStart_4116581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4116581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4116581 prefixEnd_4116581 := by exact prefixLift 4116581
  have htrace : WordTrace (prefixWord ++ tailWord_4116581) baseStart_4116581 baseEnd_4116581 := by
    simpa [prefixWord, tailWord_4116581, baseEnd_4116581] using wordTrace_append hprefix tailTrace_4116581
  have hstable : (prefixWord ++ tailWord_4116581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4116581).length < 2 ^ (prefixWord ++ tailWord_4116581).sum := by decide
  have hdescent : baseEnd_4116581 < baseStart_4116581 := by decide
  rcases family_descends (prefixWord ++ tailWord_4116581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4116598 : List Nat := [5, 1, 1, 2, 1, 2, 2, 4, 1, 2, 2]
def baseStart_4116598 : Nat := 118140960795 + 4116598 * 2 ^ 59
def prefixEnd_4116598 : Nat := 4983230072969 + 3 ^ 40 * 4116598 * 2
def baseEnd_4116598 : Nat := 2113793435337390025093117

theorem tailTrace_4116598 : CollatzResearch.WordTrace tailWord_4116598 prefixEnd_4116598 2113793435337390025093117 := by
  unfold tailWord_4116598
  simp only [CollatzResearch.WordTrace]
  refine ⟨9384041496267248738132903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 100096442626850653206750965 9384041496267248738132903)
  ·
    refine ⟨14076062244400873107199355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9384041496267248738132903 14076062244400873107199355)
    ·
      refine ⟨21114093366601309660799033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14076062244400873107199355 21114093366601309660799033)
      ·
        refine ⟨15835570024950982245599275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21114093366601309660799033 15835570024950982245599275)
        ·
          refine ⟨23753355037426473368398913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15835570024950982245599275 23753355037426473368398913)
          ·
            refine ⟨17815016278069855026299185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23753355037426473368398913 17815016278069855026299185)
            ·
              refine ⟨13361262208552391269724389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17815016278069855026299185 13361262208552391269724389)
              ·
                refine ⟨2505236664103573363073323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13361262208552391269724389 2505236664103573363073323)
                ·
                  refine ⟨3757854996155360044609985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2505236664103573363073323 3757854996155360044609985)
                  ·
                    refine ⟨2818391247116520033457489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3757854996155360044609985 2818391247116520033457489)
                    ·
                      refine ⟨2113793435337390025093117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2818391247116520033457489 2113793435337390025093117)
                      ·
                        rfl

theorem cell23_4116598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 2, 4, 1, 2, 2].length) (baseStart_4116598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4116598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4116598 prefixEnd_4116598 := by exact prefixLift 4116598
  have htrace : WordTrace (prefixWord ++ tailWord_4116598) baseStart_4116598 baseEnd_4116598 := by
    simpa [prefixWord, tailWord_4116598, baseEnd_4116598] using wordTrace_append hprefix tailTrace_4116598
  have hstable : (prefixWord ++ tailWord_4116598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4116598).length < 2 ^ (prefixWord ++ tailWord_4116598).sum := by decide
  have hdescent : baseEnd_4116598 < baseStart_4116598 := by decide
  rcases family_descends (prefixWord ++ tailWord_4116598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4116624 : List Nat := [2, 1, 1, 1, 1, 1, 8, 2, 1, 3, 2]
def baseStart_4116624 : Nat := 118140960795 + 4116624 * 2 ^ 59
def prefixEnd_4116624 : Nat := 4983230072969 + 3 ^ 40 * 4116624 * 2
def baseEnd_4116624 : Nat := 2113806785834406923367997

theorem tailTrace_4116624 : CollatzResearch.WordTrace tailWord_4116624 prefixEnd_4116624 2113806785834406923367997 := by
  unfold tailWord_4116624
  simp only [CollatzResearch.WordTrace]
  refine ⟨75072806119090893125286463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100097074825454524167048617 75072806119090893125286463)
  ·
    refine ⟨112609209178636339687929695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75072806119090893125286463 112609209178636339687929695)
    ·
      refine ⟨168913813767954509531894543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112609209178636339687929695 168913813767954509531894543)
      ·
        refine ⟨253370720651931764297841815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168913813767954509531894543 253370720651931764297841815)
        ·
          refine ⟨380056080977897646446762723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 253370720651931764297841815 380056080977897646446762723)
          ·
            refine ⟨570084121466846469670144085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 380056080977897646446762723 570084121466846469670144085)
            ·
              refine ⟨6680673298439607066447001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 570084121466846469670144085 6680673298439607066447001)
              ·
                refine ⟨5010504973829705299835251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6680673298439607066447001 5010504973829705299835251)
                ·
                  refine ⟨7515757460744557949752877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5010504973829705299835251 7515757460744557949752877)
                  ·
                    refine ⟨2818409047779209231157329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7515757460744557949752877 2818409047779209231157329)
                    ·
                      refine ⟨2113806785834406923367997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2818409047779209231157329 2113806785834406923367997)
                      ·
                        rfl

theorem cell23_4116624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 8, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 8, 2, 1, 3, 2].length) (baseStart_4116624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4116624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4116624 prefixEnd_4116624 := by exact prefixLift 4116624
  have htrace : WordTrace (prefixWord ++ tailWord_4116624) baseStart_4116624 baseEnd_4116624 := by
    simpa [prefixWord, tailWord_4116624, baseEnd_4116624] using wordTrace_append hprefix tailTrace_4116624
  have hstable : (prefixWord ++ tailWord_4116624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4116624).length < 2 ^ (prefixWord ++ tailWord_4116624).sum := by decide
  have hdescent : baseEnd_4116624 < baseStart_4116624 := by decide
  rcases family_descends (prefixWord ++ tailWord_4116624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4116640 : List Nat := [2, 1, 1, 4, 2, 2, 1, 1, 1, 3, 5]
def baseStart_4116640 : Nat := 118140960795 + 4116640 * 2 ^ 59
def prefixEnd_4116640 : Nat := 4983230072969 + 3 ^ 40 * 4116640 * 2
def baseEnd_4116640 : Nat := 2113815001524878860767923

theorem tailTrace_4116640 : CollatzResearch.WordTrace tailWord_4116640 prefixEnd_4116640 2113815001524878860767923 := by
  unfold tailWord_4116640
  simp only [CollatzResearch.WordTrace]
  refine ⟨75073097903061910491577687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100097463870749213988770249 75073097903061910491577687)
  ·
    refine ⟨112609646854592865737366531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75073097903061910491577687 112609646854592865737366531)
    ·
      refine ⟨168914470281889298606049797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112609646854592865737366531 168914470281889298606049797)
      ·
        refine ⟨31671463177854243488634337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 168914470281889298606049797 31671463177854243488634337)
        ·
          refine ⟨23753597383390682616475753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31671463177854243488634337 23753597383390682616475753)
          ·
            refine ⟨17815198037543011962356815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23753597383390682616475753 17815198037543011962356815)
            ·
              refine ⟨26722797056314517943535223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17815198037543011962356815 26722797056314517943535223)
              ·
                refine ⟨40084195584471776915302835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26722797056314517943535223 40084195584471776915302835)
                ·
                  refine ⟨60126293376707665372954253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40084195584471776915302835 60126293376707665372954253)
                  ·
                    refine ⟨22547360016265374514857845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 60126293376707665372954253 22547360016265374514857845)
                    ·
                      refine ⟨2113815001524878860767923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22547360016265374514857845 2113815001524878860767923)
                      ·
                        rfl

theorem cell23_4116640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 1, 1, 1, 3, 5].length) (baseStart_4116640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4116640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4116640 prefixEnd_4116640 := by exact prefixLift 4116640
  have htrace : WordTrace (prefixWord ++ tailWord_4116640) baseStart_4116640 baseEnd_4116640 := by
    simpa [prefixWord, tailWord_4116640, baseEnd_4116640] using wordTrace_append hprefix tailTrace_4116640
  have hstable : (prefixWord ++ tailWord_4116640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4116640).length < 2 ^ (prefixWord ++ tailWord_4116640).sum := by decide
  have hdescent : baseEnd_4116640 < baseStart_4116640 := by decide
  rcases family_descends (prefixWord ++ tailWord_4116640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4116711 : List Nat := [1, 1, 5, 3, 1, 1, 4, 2, 5]
def baseStart_4116711 : Nat := 118140960795 + 4116711 * 2 ^ 59
def prefixEnd_4116711 : Nat := 4983230072969 + 3 ^ 40 * 4116711 * 2
def baseEnd_4116711 : Nat := 234872384294594231442233

theorem tailTrace_4116711 : CollatzResearch.WordTrace tailWord_4116711 prefixEnd_4116711 234872384294594231442233 := by
  unfold tailWord_4116711
  simp only [CollatzResearch.WordTrace]
  refine ⟨150148785388866600108989987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100099190259244400072659991 150148785388866600108989987)
  ·
    refine ⟨225223178083299900163484981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150148785388866600108989987 225223178083299900163484981)
    ·
      refine ⟨21114672945309365640326717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 225223178083299900163484981 21114672945309365640326717)
      ·
        refine ⟨7918002354491012115122519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21114672945309365640326717 7918002354491012115122519)
        ·
          refine ⟨11877003531736518172683779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7918002354491012115122519 11877003531736518172683779)
          ·
            refine ⟨17815505297604777259025669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11877003531736518172683779 17815505297604777259025669)
            ·
              refine ⟨3340407243300895736067313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17815505297604777259025669 3340407243300895736067313)
              ·
                refine ⟨2505305432475671802050485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3340407243300895736067313 2505305432475671802050485)
                ·
                  refine ⟨234872384294594231442233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2505305432475671802050485 234872384294594231442233)
                  ·
                    rfl

theorem cell23_4116711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 4, 2, 5].length) (baseStart_4116711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4116711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4116711 prefixEnd_4116711 := by exact prefixLift 4116711
  have htrace : WordTrace (prefixWord ++ tailWord_4116711) baseStart_4116711 baseEnd_4116711 := by
    simpa [prefixWord, tailWord_4116711, baseEnd_4116711] using wordTrace_append hprefix tailTrace_4116711
  have hstable : (prefixWord ++ tailWord_4116711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4116711).length < 2 ^ (prefixWord ++ tailWord_4116711).sum := by decide
  have hdescent : baseEnd_4116711 < baseStart_4116711 := by decide
  rcases family_descends (prefixWord ++ tailWord_4116711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4116744 : List Nat := [2, 1, 3, 2, 3, 1, 3, 1, 2, 1, 4]
def baseStart_4116744 : Nat := 118140960795 + 4116744 * 2 ^ 59
def prefixEnd_4116744 : Nat := 4983230072969 + 3 ^ 40 * 4116744 * 2
def baseEnd_4116744 : Nat := 2113868403512946453867445

theorem tailTrace_4116744 : CollatzResearch.WordTrace tailWord_4116744 prefixEnd_4116744 2113868403512946453867445 := by
  unfold tailWord_4116744
  simp only [CollatzResearch.WordTrace]
  refine ⟨75074994498873523372470643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100099992665164697829960857 75074994498873523372470643)
  ·
    refine ⟨112612491748310285058705965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75074994498873523372470643 112612491748310285058705965)
    ·
      refine ⟨42229684405616356897014737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 112612491748310285058705965 42229684405616356897014737)
      ·
        refine ⟨31672263304212267672761053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42229684405616356897014737 31672263304212267672761053)
        ·
          refine ⟨11877098739079600377285395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31672263304212267672761053 11877098739079600377285395)
          ·
            refine ⟨17815648108619400565928093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11877098739079600377285395 17815648108619400565928093)
            ·
              refine ⟨6680868040732275212223035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17815648108619400565928093 6680868040732275212223035)
              ·
                refine ⟨10021302061098412818334553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6680868040732275212223035 10021302061098412818334553)
                ·
                  refine ⟨7515976545823809613750915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10021302061098412818334553 7515976545823809613750915)
                  ·
                    refine ⟨11273964818735714420626373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7515976545823809613750915 11273964818735714420626373)
                    ·
                      refine ⟨2113868403512946453867445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11273964818735714420626373 2113868403512946453867445)
                      ·
                        rfl

theorem cell23_4116744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 3, 1, 2, 1, 4].length) (baseStart_4116744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4116744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4116744 prefixEnd_4116744 := by exact prefixLift 4116744
  have htrace : WordTrace (prefixWord ++ tailWord_4116744) baseStart_4116744 baseEnd_4116744 := by
    simpa [prefixWord, tailWord_4116744, baseEnd_4116744] using wordTrace_append hprefix tailTrace_4116744
  have hstable : (prefixWord ++ tailWord_4116744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4116744).length < 2 ^ (prefixWord ++ tailWord_4116744).sum := by decide
  have hdescent : baseEnd_4116744 < baseStart_4116744 := by decide
  rcases family_descends (prefixWord ++ tailWord_4116744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4116747 : List Nat := [1, 1, 1, 1, 5, 2, 3, 1, 1, 4, 3]
def baseStart_4116747 : Nat := 118140960795 + 4116747 * 2 ^ 59
def prefixEnd_4116747 : Nat := 4983230072969 + 3 ^ 40 * 4116747 * 2
def baseEnd_4116747 : Nat := 2113869943954909942129931

theorem tailTrace_4116747 : CollatzResearch.WordTrace tailWord_4116747 prefixEnd_4116747 2113869943954909942129931 := by
  unfold tailWord_4116747
  simp only [CollatzResearch.WordTrace]
  refine ⟨150150098416736178257300495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100100065611157452171533663 150150098416736178257300495)
  ·
    refine ⟨225225147625104267385950743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150150098416736178257300495 225225147625104267385950743)
    ·
      refine ⟨337837721437656401078926115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225225147625104267385950743 337837721437656401078926115)
      ·
        refine ⟨506756582156484601618389173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 337837721437656401078926115 506756582156484601618389173)
        ·
          refine ⟨47508429577170431401723985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 506756582156484601618389173 47508429577170431401723985)
          ·
            refine ⟨35631322182877823551292989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47508429577170431401723985 35631322182877823551292989)
            ·
              refine ⟨13361745818579183831734871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35631322182877823551292989 13361745818579183831734871)
              ·
                refine ⟨20042618727868775747602307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13361745818579183831734871 20042618727868775747602307)
                ·
                  refine ⟨30063928091803163621403461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20042618727868775747602307 30063928091803163621403461)
                  ·
                    refine ⟨5636986517213093179013149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30063928091803163621403461 5636986517213093179013149)
                    ·
                      refine ⟨2113869943954909942129931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5636986517213093179013149 2113869943954909942129931)
                      ·
                        rfl

theorem cell23_4116747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 3, 1, 1, 4, 3].length) (baseStart_4116747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4116747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4116747 prefixEnd_4116747 := by exact prefixLift 4116747
  have htrace : WordTrace (prefixWord ++ tailWord_4116747) baseStart_4116747 baseEnd_4116747 := by
    simpa [prefixWord, tailWord_4116747, baseEnd_4116747] using wordTrace_append hprefix tailTrace_4116747
  have hstable : (prefixWord ++ tailWord_4116747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4116747).length < 2 ^ (prefixWord ++ tailWord_4116747).sum := by decide
  have hdescent : baseEnd_4116747 < baseStart_4116747 := by decide
  rcases family_descends (prefixWord ++ tailWord_4116747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4116767 : List Nat := [1, 1, 2, 4, 3, 2, 1, 1, 8]
def baseStart_4116767 : Nat := 118140960795 + 4116767 * 2 ^ 59
def prefixEnd_4116767 : Nat := 4983230072969 + 3 ^ 40 * 4116767 * 2
def baseEnd_4116767 : Nat := 234875579285333318208871

theorem tailTrace_4116767 : CollatzResearch.WordTrace tailWord_4116767 prefixEnd_4116767 234875579285333318208871 := by
  unfold tailWord_4116767
  simp only [CollatzResearch.WordTrace]
  refine ⟨150150827876663721673028555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100100551917775814448685703 150150827876663721673028555)
  ·
    refine ⟨225226241814995582509542833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150150827876663721673028555 225226241814995582509542833)
    ·
      refine ⟨168919681361246686882157125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 225226241814995582509542833 168919681361246686882157125)
      ·
        refine ⟨31672440255233753790404461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 168919681361246686882157125 31672440255233753790404461)
        ·
          refine ⟨11877165095712657671401673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31672440255233753790404461 11877165095712657671401673)
          ·
            refine ⟨8907873821784493253551255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11877165095712657671401673 8907873821784493253551255)
            ·
              refine ⟨13361810732676739880326883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8907873821784493253551255 13361810732676739880326883)
              ·
                refine ⟨20042716099015109820490325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13361810732676739880326883 20042716099015109820490325)
                ·
                  refine ⟨234875579285333318208871, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 20042716099015109820490325 234875579285333318208871)
                  ·
                    rfl

theorem cell23_4116767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 1, 1, 8].length) (baseStart_4116767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4116767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4116767 prefixEnd_4116767 := by exact prefixLift 4116767
  have htrace : WordTrace (prefixWord ++ tailWord_4116767) baseStart_4116767 baseEnd_4116767 := by
    simpa [prefixWord, tailWord_4116767, baseEnd_4116767] using wordTrace_append hprefix tailTrace_4116767
  have hstable : (prefixWord ++ tailWord_4116767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4116767).length < 2 ^ (prefixWord ++ tailWord_4116767).sum := by decide
  have hdescent : baseEnd_4116767 < baseStart_4116767 := by decide
  rcases family_descends (prefixWord ++ tailWord_4116767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4116811 : List Nat := [1, 1, 1, 1, 3, 1, 1, 9, 1, 1, 3]
def baseStart_4116811 : Nat := 118140960795 + 4116811 * 2 ^ 59
def prefixEnd_4116811 : Nat := 4983230072969 + 3 ^ 40 * 4116811 * 2
def baseEnd_4116811 : Nat := 2113902806716797691729637

theorem tailTrace_4116811 : CollatzResearch.WordTrace tailWord_4116811 prefixEnd_4116811 2113902806716797691729637 := by
  unfold tailWord_4116811
  simp only [CollatzResearch.WordTrace]
  refine ⟨150152432688504317187630287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100101621792336211458420191 150152432688504317187630287)
  ·
    refine ⟨225228649032756475781445431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150152432688504317187630287 225228649032756475781445431)
    ·
      refine ⟨337842973549134713672168147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225228649032756475781445431 337842973549134713672168147)
      ·
        refine ⟨506764460323702070508252221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 337842973549134713672168147 506764460323702070508252221)
        ·
          refine ⟨190036672621388276440594583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 506764460323702070508252221 190036672621388276440594583)
          ·
            refine ⟨285055008932082414660891875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 190036672621388276440594583 285055008932082414660891875)
            ·
              refine ⟨427582513398123621991337813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 285055008932082414660891875 427582513398123621991337813)
              ·
                refine ⟨2505366289442130597605495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 427582513398123621991337813 2505366289442130597605495)
                ·
                  refine ⟨3758049434163195896408243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2505366289442130597605495 3758049434163195896408243)
                  ·
                    refine ⟨5637074151244793844612365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3758049434163195896408243 5637074151244793844612365)
                    ·
                      refine ⟨2113902806716797691729637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5637074151244793844612365 2113902806716797691729637)
                      ·
                        rfl

theorem cell23_4116811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 9, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 9, 1, 1, 3].length) (baseStart_4116811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4116811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4116811 prefixEnd_4116811 := by exact prefixLift 4116811
  have htrace : WordTrace (prefixWord ++ tailWord_4116811) baseStart_4116811 baseEnd_4116811 := by
    simpa [prefixWord, tailWord_4116811, baseEnd_4116811] using wordTrace_append hprefix tailTrace_4116811
  have hstable : (prefixWord ++ tailWord_4116811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4116811).length < 2 ^ (prefixWord ++ tailWord_4116811).sum := by decide
  have hdescent : baseEnd_4116811 < baseStart_4116811 := by decide
  rcases family_descends (prefixWord ++ tailWord_4116811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4116874 : List Nat := [3, 1, 2, 5, 1, 11]
def baseStart_4116874 : Nat := 118140960795 + 4116874 * 2 ^ 59
def prefixEnd_4116874 : Nat := 4983230072969 + 3 ^ 40 * 4116874 * 2
def baseEnd_4116874 : Nat := 8699321629621526523629

theorem tailTrace_4116874 : CollatzResearch.WordTrace tailWord_4116874 prefixEnd_4116874 8699321629621526523629 := by
  unfold tailWord_4116874
  simp only [CollatzResearch.WordTrace]
  refine ⟨37538682621819019736793419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100103153658184052631449117 37538682621819019736793419)
  ·
    refine ⟨56308023932728529605190129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37538682621819019736793419 56308023932728529605190129)
    ·
      refine ⟨42231017949546397203892597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56308023932728529605190129 42231017949546397203892597)
      ·
        refine ⟨3959157932769974737864931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 42231017949546397203892597 3959157932769974737864931)
        ·
          refine ⟨5938736899154962106797397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3959157932769974737864931 5938736899154962106797397)
          ·
            refine ⟨8699321629621526523629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 5938736899154962106797397 8699321629621526523629)
            ·
              rfl

theorem cell23_4116874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 11].length) (baseStart_4116874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4116874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4116874 prefixEnd_4116874 := by exact prefixLift 4116874
  have htrace : WordTrace (prefixWord ++ tailWord_4116874) baseStart_4116874 baseEnd_4116874 := by
    simpa [prefixWord, tailWord_4116874, baseEnd_4116874] using wordTrace_append hprefix tailTrace_4116874
  have hstable : (prefixWord ++ tailWord_4116874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4116874).length < 2 ^ (prefixWord ++ tailWord_4116874).sum := by decide
  have hdescent : baseEnd_4116874 < baseStart_4116874 := by decide
  rcases family_descends (prefixWord ++ tailWord_4116874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4116878 : List Nat := [4, 1, 1, 4, 1, 2, 2, 2, 2, 4]
def baseStart_4116878 : Nat := 118140960795 + 4116878 * 2 ^ 59
def prefixEnd_4116878 : Nat := 4983230072969 + 3 ^ 40 * 4116878 * 2
def baseEnd_4116878 : Nat := 704645736640216309863943

theorem tailTrace_4116878 : CollatzResearch.WordTrace tailWord_4116878 prefixEnd_4116878 704645736640216309863943 := by
  unfold tailWord_4116878
  simp only [CollatzResearch.WordTrace]
  refine ⟨18769359547407698453789911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 100103250919507725086879525 18769359547407698453789911)
  ·
    refine ⟨28154039321111547680684867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18769359547407698453789911 28154039321111547680684867)
    ·
      refine ⟨42231058981667321521027301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28154039321111547680684867 42231058981667321521027301)
      ·
        refine ⟨7918323559062622785192619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42231058981667321521027301 7918323559062622785192619)
        ·
          refine ⟨11877485338593934177788929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7918323559062622785192619 11877485338593934177788929)
          ·
            refine ⟨8908114003945450633341697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11877485338593934177788929 8908114003945450633341697)
            ·
              refine ⟨6681085502959087975006273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8908114003945450633341697 6681085502959087975006273)
              ·
                refine ⟨5010814127219315981254705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6681085502959087975006273 5010814127219315981254705)
                ·
                  refine ⟨3758110595414486985941029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5010814127219315981254705 3758110595414486985941029)
                  ·
                    refine ⟨704645736640216309863943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3758110595414486985941029 704645736640216309863943)
                    ·
                      rfl

theorem cell23_4116878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 2, 2, 2, 4].length) (baseStart_4116878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4116878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4116878 prefixEnd_4116878 := by exact prefixLift 4116878
  have htrace : WordTrace (prefixWord ++ tailWord_4116878) baseStart_4116878 baseEnd_4116878 := by
    simpa [prefixWord, tailWord_4116878, baseEnd_4116878] using wordTrace_append hprefix tailTrace_4116878
  have hstable : (prefixWord ++ tailWord_4116878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4116878).length < 2 ^ (prefixWord ++ tailWord_4116878).sum := by decide
  have hdescent : baseEnd_4116878 < baseStart_4116878 := by decide
  rcases family_descends (prefixWord ++ tailWord_4116878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4116887 : List Nat := [1, 1, 3, 3, 1, 1, 3, 1, 2, 7]
def baseStart_4116887 : Nat := 118140960795 + 4116887 * 2 ^ 59
def prefixEnd_4116887 : Nat := 4983230072969 + 3 ^ 40 * 4116887 * 2
def baseEnd_4116887 : Nat := 704647277082179798126429

theorem tailTrace_4116887 : CollatzResearch.WordTrace tailWord_4116887 prefixEnd_4116887 704647277082179798126429 := by
  unfold tailWord_4116887
  simp only [CollatzResearch.WordTrace]
  refine ⟨150155204636228982167396915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100103469757485988111597943 150155204636228982167396915)
  ·
    refine ⟨225232806954343473251095373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150155204636228982167396915 225232806954343473251095373)
    ·
      refine ⟨84462302607878802469160765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 225232806954343473251095373 84462302607878802469160765)
      ·
        refine ⟨31673363477954550925935287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84462302607878802469160765 31673363477954550925935287)
        ·
          refine ⟨47510045216931826388902931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31673363477954550925935287 47510045216931826388902931)
          ·
            refine ⟨71265067825397739583354397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47510045216931826388902931 71265067825397739583354397)
            ·
              refine ⟨26724400434524152343757899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71265067825397739583354397 26724400434524152343757899)
              ·
                refine ⟨40086600651786228515636849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26724400434524152343757899 40086600651786228515636849)
                ·
                  refine ⟨30064950488839671386727637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40086600651786228515636849 30064950488839671386727637)
                  ·
                    refine ⟨704647277082179798126429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 30064950488839671386727637 704647277082179798126429)
                    ·
                      rfl

theorem cell23_4116887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 3, 1, 2, 7].length) (baseStart_4116887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4116887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4116887 prefixEnd_4116887 := by exact prefixLift 4116887
  have htrace : WordTrace (prefixWord ++ tailWord_4116887) baseStart_4116887 baseEnd_4116887 := by
    simpa [prefixWord, tailWord_4116887, baseEnd_4116887] using wordTrace_append hprefix tailTrace_4116887
  have hstable : (prefixWord ++ tailWord_4116887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4116887).length < 2 ^ (prefixWord ++ tailWord_4116887).sum := by decide
  have hdescent : baseEnd_4116887 < baseStart_4116887 := by decide
  rcases family_descends (prefixWord ++ tailWord_4116887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4116901 : List Nat := [1, 3, 1, 2, 1, 1, 3, 5, 2, 1, 3]
def baseStart_4116901 : Nat := 118140960795 + 4116901 * 2 ^ 59
def prefixEnd_4116901 : Nat := 4983230072969 + 3 ^ 40 * 4116901 * 2
def baseEnd_4116901 : Nat := 2113949019975702339604223

theorem tailTrace_4116901 : CollatzResearch.WordTrace tailWord_4116901 prefixEnd_4116901 2113949019975702339604223 := by
  unfold tailWord_4116901
  simp only [CollatzResearch.WordTrace]
  refine ⟨150155715258178262558406557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100103810172118841705604371 150155715258178262558406557)
  ·
    refine ⟨56308393221816848459402459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 150155715258178262558406557 56308393221816848459402459)
    ·
      refine ⟨84462589832725272689103689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56308393221816848459402459 84462589832725272689103689)
      ·
        refine ⟨63346942374543954516827767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84462589832725272689103689 63346942374543954516827767)
        ·
          refine ⟨95020413561815931775241651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63346942374543954516827767 95020413561815931775241651)
          ·
            refine ⟨142530620342723897662862477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95020413561815931775241651 142530620342723897662862477)
            ·
              refine ⟨53448982628521461623573429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 142530620342723897662862477 53448982628521461623573429)
              ·
                refine ⟨5010842121423887027210009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 53448982628521461623573429 5010842121423887027210009)
                ·
                  refine ⟨3758131591067915270407507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5010842121423887027210009 3758131591067915270407507)
                  ·
                    refine ⟨5637197386601872905611261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3758131591067915270407507 5637197386601872905611261)
                    ·
                      refine ⟨2113949019975702339604223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5637197386601872905611261 2113949019975702339604223)
                      ·
                        rfl

theorem cell23_4116901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 5, 2, 1, 3].length) (baseStart_4116901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4116901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4116901 prefixEnd_4116901 := by exact prefixLift 4116901
  have htrace : WordTrace (prefixWord ++ tailWord_4116901) baseStart_4116901 baseEnd_4116901 := by
    simpa [prefixWord, tailWord_4116901, baseEnd_4116901] using wordTrace_append hprefix tailTrace_4116901
  have hstable : (prefixWord ++ tailWord_4116901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4116901).length < 2 ^ (prefixWord ++ tailWord_4116901).sum := by decide
  have hdescent : baseEnd_4116901 < baseStart_4116901 := by decide
  rcases family_descends (prefixWord ++ tailWord_4116901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4116929 : List Nat := [1, 2, 7, 1, 2, 1, 1, 2, 2, 4]
def baseStart_4116929 : Nat := 118140960795 + 4116929 * 2 ^ 59
def prefixEnd_4116929 : Nat := 4983230072969 + 3 ^ 40 * 4116929 * 2
def baseEnd_4116929 : Nat := 704654465811342743351365

theorem tailTrace_4116929 : CollatzResearch.WordTrace tailWord_4116929 prefixEnd_4116929 704654465811342743351365 := by
  unfold tailWord_4116929
  simp only [CollatzResearch.WordTrace]
  refine ⟨150156736502076823340425841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100104491001384548893617227 150156736502076823340425841)
  ·
    refine ⟨112617552376557617505319381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150156736502076823340425841 112617552376557617505319381)
    ·
      refine ⟨2639473883825569160280923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 112617552376557617505319381 2639473883825569160280923)
      ·
        refine ⟨3959210825738353740421385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2639473883825569160280923 3959210825738353740421385)
        ·
          refine ⟨2969408119303765305316039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3959210825738353740421385 2969408119303765305316039)
          ·
            refine ⟨4454112178955647957974059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2969408119303765305316039 4454112178955647957974059)
            ·
              refine ⟨6681168268433471936961089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4454112178955647957974059 6681168268433471936961089)
              ·
                refine ⟨5010876201325103952720817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6681168268433471936961089 5010876201325103952720817)
                ·
                  refine ⟨3758157150993827964540613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5010876201325103952720817 3758157150993827964540613)
                  ·
                    refine ⟨704654465811342743351365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3758157150993827964540613 704654465811342743351365)
                    ·
                      rfl

theorem cell23_4116929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 2, 1, 1, 2, 2, 4].length) (baseStart_4116929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4116929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4116929 prefixEnd_4116929 := by exact prefixLift 4116929
  have htrace : WordTrace (prefixWord ++ tailWord_4116929) baseStart_4116929 baseEnd_4116929 := by
    simpa [prefixWord, tailWord_4116929, baseEnd_4116929] using wordTrace_append hprefix tailTrace_4116929
  have hstable : (prefixWord ++ tailWord_4116929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4116929).length < 2 ^ (prefixWord ++ tailWord_4116929).sum := by decide
  have hdescent : baseEnd_4116929 < baseStart_4116929 := by decide
  rcases family_descends (prefixWord ++ tailWord_4116929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4116954 : List Nat := [3, 1, 1, 2, 3, 1, 1, 3, 2, 2, 4]
def baseStart_4116954 : Nat := 118140960795 + 4116954 * 2 ^ 59
def prefixEnd_4116954 : Nat := 4983230072969 + 3 ^ 40 * 4116954 * 2
def baseEnd_4116954 : Nat := 2113976234450390632241479

theorem tailTrace_4116954 : CollatzResearch.WordTrace tailWord_4116954 prefixEnd_4116954 2113976234450390632241479 := by
  unfold tailWord_4116954
  simp only [CollatzResearch.WordTrace]
  refine ⟨37539412081746563152521479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100105098884657501740057277 37539412081746563152521479)
  ·
    refine ⟨56309118122619844728782219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37539412081746563152521479 56309118122619844728782219)
    ·
      refine ⟨84463677183929767093173329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56309118122619844728782219 84463677183929767093173329)
      ·
        refine ⟨63347757887947325319879997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84463677183929767093173329 63347757887947325319879997)
        ·
          refine ⟨23755409207980246994954999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63347757887947325319879997 23755409207980246994954999)
          ·
            refine ⟨35633113811970370492432499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23755409207980246994954999 35633113811970370492432499)
            ·
              refine ⟨53449670717955555738648749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35633113811970370492432499 53449670717955555738648749)
              ·
                refine ⟨20043626519233333401993281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53449670717955555738648749 20043626519233333401993281)
                ·
                  refine ⟨15032719889425000051494961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20043626519233333401993281 15032719889425000051494961)
                  ·
                    refine ⟨11274539917068750038621221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15032719889425000051494961 11274539917068750038621221)
                    ·
                      refine ⟨2113976234450390632241479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11274539917068750038621221 2113976234450390632241479)
                      ·
                        rfl

theorem cell23_4116954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 3, 2, 2, 4].length) (baseStart_4116954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4116954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4116954 prefixEnd_4116954 := by exact prefixLift 4116954
  have htrace : WordTrace (prefixWord ++ tailWord_4116954) baseStart_4116954 baseEnd_4116954 := by
    simpa [prefixWord, tailWord_4116954, baseEnd_4116954] using wordTrace_append hprefix tailTrace_4116954
  have hstable : (prefixWord ++ tailWord_4116954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4116954).length < 2 ^ (prefixWord ++ tailWord_4116954).sum := by decide
  have hdescent : baseEnd_4116954 < baseStart_4116954 := by decide
  rcases family_descends (prefixWord ++ tailWord_4116954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4117004 : List Nat := [2, 2, 1, 2, 4, 1, 1, 1, 1, 1, 7]
def baseStart_4117004 : Nat := 118140960795 + 4117004 * 2 ^ 59
def prefixEnd_4117004 : Nat := 4983230072969 + 3 ^ 40 * 4117004 * 2
def baseEnd_4117004 : Nat := 2114001908483115436616249

theorem tailTrace_4117004 : CollatzResearch.WordTrace tailWord_4117004 prefixEnd_4117004 2114001908483115436616249 := by
  unfold tailWord_4117004
  simp only [CollatzResearch.WordTrace]
  refine ⟨75079735988402555574703033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100106314651203407432937377 75079735988402555574703033)
  ·
    refine ⟨56309801991301916681027275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75079735988402555574703033 56309801991301916681027275)
    ·
      refine ⟨84464702986952875021540913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56309801991301916681027275 84464702986952875021540913)
      ·
        refine ⟨63348527240214656266155685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84464702986952875021540913 63348527240214656266155685)
        ·
          refine ⟨11877848857540248049904191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 63348527240214656266155685 11877848857540248049904191)
          ·
            refine ⟨17816773286310372074856287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11877848857540248049904191 17816773286310372074856287)
            ·
              refine ⟨26725159929465558112284431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17816773286310372074856287 26725159929465558112284431)
              ·
                refine ⟨40087739894198337168426647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26725159929465558112284431 40087739894198337168426647)
                ·
                  refine ⟨60131609841297505752639971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40087739894198337168426647 60131609841297505752639971)
                  ·
                    refine ⟨90197414761946258628959957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 60131609841297505752639971 90197414761946258628959957)
                    ·
                      refine ⟨2114001908483115436616249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 90197414761946258628959957 2114001908483115436616249)
                      ·
                        rfl

theorem cell23_4117004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 1, 1, 1, 1, 7].length) (baseStart_4117004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4117004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4117004 prefixEnd_4117004 := by exact prefixLift 4117004
  have htrace : WordTrace (prefixWord ++ tailWord_4117004) baseStart_4117004 baseEnd_4117004 := by
    simpa [prefixWord, tailWord_4117004, baseEnd_4117004] using wordTrace_append hprefix tailTrace_4117004
  have hstable : (prefixWord ++ tailWord_4117004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4117004).length < 2 ^ (prefixWord ++ tailWord_4117004).sum := by decide
  have hdescent : baseEnd_4117004 < baseStart_4117004 := by decide
  rcases family_descends (prefixWord ++ tailWord_4117004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4117098 : List Nat := [3, 1, 3, 2, 1, 1, 1, 2, 5, 1, 3]
def baseStart_4117098 : Nat := 118140960795 + 4117098 * 2 ^ 59
def prefixEnd_4117098 : Nat := 4983230072969 + 3 ^ 40 * 4117098 * 2
def baseEnd_4117098 : Nat := 2114050175664638068840817

theorem tailTrace_4117098 : CollatzResearch.WordTrace tailWord_4117098 prefixEnd_4117098 2114050175664638068840817 := by
  unfold tailWord_4117098
  simp only [CollatzResearch.WordTrace]
  refine ⟨37540725109616141300831987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100108600292309710135551965 37540725109616141300831987)
  ·
    refine ⟨56311087664424211951247981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37540725109616141300831987 56311087664424211951247981)
    ·
      refine ⟨21116657874159079481717993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56311087664424211951247981 21116657874159079481717993)
      ·
        refine ⟨15837493405619309611288495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21116657874159079481717993 15837493405619309611288495)
        ·
          refine ⟨23756240108428964416932743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15837493405619309611288495 23756240108428964416932743)
          ·
            refine ⟨35634360162643446625399115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23756240108428964416932743 35634360162643446625399115)
            ·
              refine ⟨53451540243965169938098673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35634360162643446625399115 53451540243965169938098673)
              ·
                refine ⟨40088655182973877453574005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53451540243965169938098673 40088655182973877453574005)
                ·
                  refine ⟨3758311423403801011272563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 40088655182973877453574005 3758311423403801011272563)
                  ·
                    refine ⟨5637467135105701516908845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3758311423403801011272563 5637467135105701516908845)
                    ·
                      refine ⟨2114050175664638068840817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5637467135105701516908845 2114050175664638068840817)
                      ·
                        rfl

theorem cell23_4117098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 2, 5, 1, 3].length) (baseStart_4117098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4117098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4117098 prefixEnd_4117098 := by exact prefixLift 4117098
  have htrace : WordTrace (prefixWord ++ tailWord_4117098) baseStart_4117098 baseEnd_4117098 := by
    simpa [prefixWord, tailWord_4117098, baseEnd_4117098] using wordTrace_append hprefix tailTrace_4117098
  have hstable : (prefixWord ++ tailWord_4117098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4117098).length < 2 ^ (prefixWord ++ tailWord_4117098).sum := by decide
  have hdescent : baseEnd_4117098 < baseStart_4117098 := by decide
  rcases family_descends (prefixWord ++ tailWord_4117098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4117148 : List Nat := [2, 2, 3, 2, 2, 1, 1, 2, 4, 4]
def baseStart_4117148 : Nat := 118140960795 + 4117148 * 2 ^ 59
def prefixEnd_4117148 : Nat := 4983230072969 + 3 ^ 40 * 4117148 * 2
def baseEnd_4117148 : Nat := 704691949899120957738529

theorem tailTrace_4117148 : CollatzResearch.WordTrace tailWord_4117148 prefixEnd_4117148 704691949899120957738529 := by
  unfold tailWord_4117148
  simp only [CollatzResearch.WordTrace]
  refine ⟨75082362044141711871324049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100109816058855615828432065 75082362044141711871324049)
  ·
    refine ⟨56311771533106283903493037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75082362044141711871324049 56311771533106283903493037)
    ·
      refine ⟨21116914324914856463809889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56311771533106283903493037 21116914324914856463809889)
      ·
        refine ⟨15837685743686142347857417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21116914324914856463809889 15837685743686142347857417)
        ·
          refine ⟨11878264307764606760893063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15837685743686142347857417 11878264307764606760893063)
          ·
            refine ⟨17817396461646910141339595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11878264307764606760893063 17817396461646910141339595)
            ·
              refine ⟨26726094692470365212009393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17817396461646910141339595 26726094692470365212009393)
              ·
                refine ⟨20044571019352773909007045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26726094692470365212009393 20044571019352773909007045)
                ·
                  refine ⟨3758357066128645107938821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20044571019352773909007045 3758357066128645107938821)
                  ·
                    refine ⟨704691949899120957738529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3758357066128645107938821 704691949899120957738529)
                    ·
                      rfl

theorem cell23_4117148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 1, 2, 4, 4].length) (baseStart_4117148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4117148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4117148 prefixEnd_4117148 := by exact prefixLift 4117148
  have htrace : WordTrace (prefixWord ++ tailWord_4117148) baseStart_4117148 baseEnd_4117148 := by
    simpa [prefixWord, tailWord_4117148, baseEnd_4117148] using wordTrace_append hprefix tailTrace_4117148
  have hstable : (prefixWord ++ tailWord_4117148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4117148).length < 2 ^ (prefixWord ++ tailWord_4117148).sum := by decide
  have hdescent : baseEnd_4117148 < baseStart_4117148 := by decide
  rcases family_descends (prefixWord ++ tailWord_4117148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4117166 : List Nat := [4, 1, 4, 1, 1, 2, 3, 2, 1, 1, 3]
def baseStart_4117166 : Nat := 118140960795 + 4117166 * 2 ^ 59
def prefixEnd_4117166 : Nat := 4983230072969 + 3 ^ 40 * 4117166 * 2
def baseEnd_4117166 : Nat := 2114085092349143802790505

theorem tailTrace_4117166 : CollatzResearch.WordTrace tailWord_4117166 prefixEnd_4117166 2114085092349143802790505 := by
  unfold tailWord_4117166
  simp only [CollatzResearch.WordTrace]
  refine ⟨18770672575277276602100419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 100110253734812141877868901 18770672575277276602100419)
  ·
    refine ⟨28156008862915914903150629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18770672575277276602100419 28156008862915914903150629)
    ·
      refine ⟨5279251661796734044340743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28156008862915914903150629 5279251661796734044340743)
      ·
        refine ⟨7918877492695101066511115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5279251661796734044340743 7918877492695101066511115)
        ·
          refine ⟨11878316239042651599766673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7918877492695101066511115 11878316239042651599766673)
          ·
            refine ⟨8908737179281988699825005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11878316239042651599766673 8908737179281988699825005)
            ·
              refine ⟨3340776442230745762434377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8908737179281988699825005 3340776442230745762434377)
              ·
                refine ⟨2505582331673059321825783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3340776442230745762434377 2505582331673059321825783)
                ·
                  refine ⟨3758373497509588982738675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2505582331673059321825783 3758373497509588982738675)
                  ·
                    refine ⟨5637560246264383474108013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3758373497509588982738675 5637560246264383474108013)
                    ·
                      refine ⟨2114085092349143802790505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5637560246264383474108013 2114085092349143802790505)
                      ·
                        rfl

theorem cell23_4117166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 3, 2, 1, 1, 3].length) (baseStart_4117166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4117166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4117166 prefixEnd_4117166 := by exact prefixLift 4117166
  have htrace : WordTrace (prefixWord ++ tailWord_4117166) baseStart_4117166 baseEnd_4117166 := by
    simpa [prefixWord, tailWord_4117166, baseEnd_4117166] using wordTrace_append hprefix tailTrace_4117166
  have hstable : (prefixWord ++ tailWord_4117166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4117166).length < 2 ^ (prefixWord ++ tailWord_4117166).sum := by decide
  have hdescent : baseEnd_4117166 < baseStart_4117166 := by decide
  rcases family_descends (prefixWord ++ tailWord_4117166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4117228 : List Nat := [2, 2, 1, 1, 2, 2, 1, 1, 5, 4, 2]
def baseStart_4117228 : Nat := 118140960795 + 4117228 * 2 ^ 59
def prefixEnd_4117228 : Nat := 4983230072969 + 3 ^ 40 * 4117228 * 2
def baseEnd_4117228 : Nat := 2114116928149722560215219

theorem tailTrace_4117228 : CollatzResearch.WordTrace tailWord_4117228 prefixEnd_4117228 2114116928149722560215219 := by
  unfold tailWord_4117228
  simp only [CollatzResearch.WordTrace]
  refine ⟨75083820963996798702780169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100111761285329064937040225 75083820963996798702780169)
  ·
    refine ⟨56312865722997599027085127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75083820963996798702780169 56312865722997599027085127)
    ·
      refine ⟨84469298584496398540627691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56312865722997599027085127 84469298584496398540627691)
      ·
        refine ⟨126703947876744597810941537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84469298584496398540627691 126703947876744597810941537)
        ·
          refine ⟨95027960907558448358206153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126703947876744597810941537 95027960907558448358206153)
          ·
            refine ⟨71270970680668836268654615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95027960907558448358206153 71270970680668836268654615)
            ·
              refine ⟨106906456021003254402981923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71270970680668836268654615 106906456021003254402981923)
              ·
                refine ⟨160359684031504881604472885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 106906456021003254402981923 160359684031504881604472885)
                ·
                  refine ⟨15033720377953582650419333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 160359684031504881604472885 15033720377953582650419333)
                  ·
                    refine ⟨2818822570866296746953625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15033720377953582650419333 2818822570866296746953625)
                    ·
                      refine ⟨2114116928149722560215219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2818822570866296746953625 2114116928149722560215219)
                      ·
                        rfl

theorem cell23_4117228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 4, 2].length) (baseStart_4117228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4117228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4117228 prefixEnd_4117228 := by exact prefixLift 4117228
  have htrace : WordTrace (prefixWord ++ tailWord_4117228) baseStart_4117228 baseEnd_4117228 := by
    simpa [prefixWord, tailWord_4117228, baseEnd_4117228] using wordTrace_append hprefix tailTrace_4117228
  have hstable : (prefixWord ++ tailWord_4117228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4117228).length < 2 ^ (prefixWord ++ tailWord_4117228).sum := by decide
  have hdescent : baseEnd_4117228 < baseStart_4117228 := by decide
  rcases family_descends (prefixWord ++ tailWord_4117228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4117238 : List Nat := [5, 1, 1, 1, 1, 2, 3, 1, 2, 6]
def baseStart_4117238 : Nat := 118140960795 + 4117238 * 2 ^ 59
def prefixEnd_4117238 : Nat := 4983230072969 + 3 ^ 40 * 4117238 * 2
def baseEnd_4117238 : Nat := 704707354318755840363391

theorem tailTrace_4117238 : CollatzResearch.WordTrace tailWord_4117238 prefixEnd_4117238 704707354318755840363391 := by
  unfold tailWord_4117238
  simp only [CollatzResearch.WordTrace]
  refine ⟨9385500416122335569589023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 100112004438638246075616245 9385500416122335569589023)
  ·
    refine ⟨14078250624183503354383535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9385500416122335569589023 14078250624183503354383535)
    ·
      refine ⟨21117375936275255031575303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14078250624183503354383535 21117375936275255031575303)
      ·
        refine ⟨31676063904412882547362955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21117375936275255031575303 31676063904412882547362955)
        ·
          refine ⟨47514095856619323821044433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31676063904412882547362955 47514095856619323821044433)
          ·
            refine ⟨35635571892464492865783325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47514095856619323821044433 35635571892464492865783325)
            ·
              refine ⟨13363339459674184824668747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35635571892464492865783325 13363339459674184824668747)
              ·
                refine ⟨20045009189511277237003121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13363339459674184824668747 20045009189511277237003121)
                ·
                  refine ⟨15033756892133457927752341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20045009189511277237003121 15033756892133457927752341)
                  ·
                    refine ⟨704707354318755840363391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15033756892133457927752341 704707354318755840363391)
                    ·
                      rfl

theorem cell23_4117238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 3, 1, 2, 6].length) (baseStart_4117238 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4117238 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4117238 prefixEnd_4117238 := by exact prefixLift 4117238
  have htrace : WordTrace (prefixWord ++ tailWord_4117238) baseStart_4117238 baseEnd_4117238 := by
    simpa [prefixWord, tailWord_4117238, baseEnd_4117238] using wordTrace_append hprefix tailTrace_4117238
  have hstable : (prefixWord ++ tailWord_4117238).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4117238).length < 2 ^ (prefixWord ++ tailWord_4117238).sum := by decide
  have hdescent : baseEnd_4117238 < baseStart_4117238 := by decide
  rcases family_descends (prefixWord ++ tailWord_4117238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4117245 : List Nat := [1, 4, 1, 1, 1, 1, 6, 1, 1, 4, 2]
def baseStart_4117245 : Nat := 118140960795 + 4117245 * 2 ^ 59
def prefixEnd_4117245 : Nat := 4983230072969 + 3 ^ 40 * 4117245 * 2
def baseEnd_4117245 : Nat := 2114125657320848993702641

theorem tailTrace_4117245 : CollatzResearch.WordTrace tailWord_4117245 prefixEnd_4117245 2114125657320848993702641 := by
  unfold tailWord_4117245
  simp only [CollatzResearch.WordTrace]
  refine ⟨150168261968932009308929189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100112174645954672872619459 150168261968932009308929189)
  ·
    refine ⟨28156549119174751745424223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 150168261968932009308929189 28156549119174751745424223)
    ·
      refine ⟨42234823678762127618136335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28156549119174751745424223 42234823678762127618136335)
      ·
        refine ⟨63352235518143191427204503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42234823678762127618136335 63352235518143191427204503)
        ·
          refine ⟨95028353277214787140806755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63352235518143191427204503 95028353277214787140806755)
          ·
            refine ⟨142542529915822180711210133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95028353277214787140806755 142542529915822180711210133)
            ·
              refine ⟨6681681089804164720837975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 142542529915822180711210133 6681681089804164720837975)
              ·
                refine ⟨10022521634706247081256963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6681681089804164720837975 10022521634706247081256963)
                ·
                  refine ⟨15033782452059370621885445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10022521634706247081256963 15033782452059370621885445)
                  ·
                    refine ⟨2818834209761131991603521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15033782452059370621885445 2818834209761131991603521)
                    ·
                      refine ⟨2114125657320848993702641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2818834209761131991603521 2114125657320848993702641)
                      ·
                        rfl

theorem cell23_4117245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 6, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 6, 1, 1, 4, 2].length) (baseStart_4117245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4117245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4117245 prefixEnd_4117245 := by exact prefixLift 4117245
  have htrace : WordTrace (prefixWord ++ tailWord_4117245) baseStart_4117245 baseEnd_4117245 := by
    simpa [prefixWord, tailWord_4117245, baseEnd_4117245] using wordTrace_append hprefix tailTrace_4117245
  have hstable : (prefixWord ++ tailWord_4117245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4117245).length < 2 ^ (prefixWord ++ tailWord_4117245).sum := by decide
  have hdescent : baseEnd_4117245 < baseStart_4117245 := by decide
  rcases family_descends (prefixWord ++ tailWord_4117245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4117279 : List Nat := [1, 1, 2, 4, 2, 4, 1, 2, 2, 2, 2]
def baseStart_4117279 : Nat := 118140960795 + 4117279 * 2 ^ 59
def prefixEnd_4117279 : Nat := 4983230072969 + 3 ^ 40 * 4117279 * 2
def baseEnd_4117279 : Nat := 2114143115663101860677485

theorem tailTrace_4117279 : CollatzResearch.WordTrace tailWord_4117279 prefixEnd_4117279 2114143115663101860677485 := by
  unfold tailWord_4117279
  simp only [CollatzResearch.WordTrace]
  refine ⟨150169502050808833115666891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100113001367205888743777927 150169502050808833115666891)
  ·
    refine ⟨225254253076213249673500337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150169502050808833115666891 225254253076213249673500337)
    ·
      refine ⟨168940689807159937255125253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 225254253076213249673500337 168940689807159937255125253)
      ·
        refine ⟨31676379338842488235335985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 168940689807159937255125253 31676379338842488235335985)
        ·
          refine ⟨23757284504131866176501989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31676379338842488235335985 23757284504131866176501989)
          ·
            refine ⟨4454490844524724908094123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23757284504131866176501989 4454490844524724908094123)
            ·
              refine ⟨6681736266787087362141185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4454490844524724908094123 6681736266787087362141185)
              ·
                refine ⟨5011302200090315521605889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6681736266787087362141185 5011302200090315521605889)
                ·
                  refine ⟨3758476650067736641204417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5011302200090315521605889 3758476650067736641204417)
                  ·
                    refine ⟨2818857487550802480903313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3758476650067736641204417 2818857487550802480903313)
                    ·
                      refine ⟨2114143115663101860677485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2818857487550802480903313 2114143115663101860677485)
                      ·
                        rfl

theorem cell23_4117279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 4, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 4, 1, 2, 2, 2, 2].length) (baseStart_4117279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4117279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4117279 prefixEnd_4117279 := by exact prefixLift 4117279
  have htrace : WordTrace (prefixWord ++ tailWord_4117279) baseStart_4117279 baseEnd_4117279 := by
    simpa [prefixWord, tailWord_4117279, baseEnd_4117279] using wordTrace_append hprefix tailTrace_4117279
  have hstable : (prefixWord ++ tailWord_4117279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4117279).length < 2 ^ (prefixWord ++ tailWord_4117279).sum := by decide
  have hdescent : baseEnd_4117279 < baseStart_4117279 := by decide
  rcases family_descends (prefixWord ++ tailWord_4117279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4117328 : List Nat := [2, 1, 1, 1, 1, 4, 2, 2, 5, 4]
def baseStart_4117328 : Nat := 118140960795 + 4117328 * 2 ^ 59
def prefixEnd_4117328 : Nat := 4983230072969 + 3 ^ 40 * 4117328 * 2
def baseEnd_4117328 : Nat := 704722758738390722988253

theorem tailTrace_4117328 : CollatzResearch.WordTrace tailWord_4117328 prefixEnd_4117328 704722758738390722988253 := by
  unfold tailWord_4117328
  simp only [CollatzResearch.WordTrace]
  refine ⟨75085644613815657242100319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100114192818420876322800425 75085644613815657242100319)
  ·
    refine ⟨112628466920723485863150479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75085644613815657242100319 112628466920723485863150479)
    ·
      refine ⟨168942700381085228794725719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112628466920723485863150479 168942700381085228794725719)
      ·
        refine ⟨253414050571627843192088579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168942700381085228794725719 253414050571627843192088579)
        ·
          refine ⟨380121075857441764788132869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 253414050571627843192088579 380121075857441764788132869)
          ·
            refine ⟨71272701723270330897774913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 380121075857441764788132869 71272701723270330897774913)
            ·
              refine ⟨53454526292452748173331185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71272701723270330897774913 53454526292452748173331185)
              ·
                refine ⟨40090894719339561129998389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53454526292452748173331185 40090894719339561129998389)
                ·
                  refine ⟨3758521379938083855937349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 40090894719339561129998389 3758521379938083855937349)
                  ·
                    refine ⟨704722758738390722988253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3758521379938083855937349 704722758738390722988253)
                    ·
                      rfl

theorem cell23_4117328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 2, 5, 4].length) (baseStart_4117328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4117328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4117328 prefixEnd_4117328 := by exact prefixLift 4117328
  have htrace : WordTrace (prefixWord ++ tailWord_4117328) baseStart_4117328 baseEnd_4117328 := by
    simpa [prefixWord, tailWord_4117328, baseEnd_4117328] using wordTrace_append hprefix tailTrace_4117328
  have hstable : (prefixWord ++ tailWord_4117328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4117328).length < 2 ^ (prefixWord ++ tailWord_4117328).sum := by decide
  have hdescent : baseEnd_4117328 < baseStart_4117328 := by decide
  rcases family_descends (prefixWord ++ tailWord_4117328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4117331 : List Nat := [1, 1, 1, 2, 1, 1, 3, 3, 1, 3, 6]
def baseStart_4117331 : Nat := 118140960795 + 4117331 * 2 ^ 59
def prefixEnd_4117331 : Nat := 4983230072969 + 3 ^ 40 * 4117331 * 2
def baseEnd_4117331 : Nat := 2114169816657135657227245

theorem tailTrace_4117331 : CollatzResearch.WordTrace tailWord_4117331 prefixEnd_4117331 2114169816657135657227245 := by
  unfold tailWord_4117331
  simp only [CollatzResearch.WordTrace]
  refine ⟨150171398646620445996559847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100114265764413630664373231 150171398646620445996559847)
  ·
    refine ⟨225257097969930668994839771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150171398646620445996559847 225257097969930668994839771)
    ·
      refine ⟨337885646954896003492259657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225257097969930668994839771 337885646954896003492259657)
      ·
        refine ⟨253414235216172002619194743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 337885646954896003492259657 253414235216172002619194743)
        ·
          refine ⟨380121352824258003928792115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 253414235216172002619194743 380121352824258003928792115)
          ·
            refine ⟨570182029236387005893188173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 380121352824258003928792115 570182029236387005893188173)
            ·
              refine ⟨213818260963645127209945565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 570182029236387005893188173 213818260963645127209945565)
              ·
                refine ⟨80181847861366922703729587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 213818260963645127209945565 80181847861366922703729587)
                ·
                  refine ⟨120272771792050384055594381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 80181847861366922703729587 120272771792050384055594381)
                  ·
                    refine ⟨45102289422018894020847893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 120272771792050384055594381 45102289422018894020847893)
                    ·
                      refine ⟨2114169816657135657227245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 45102289422018894020847893 2114169816657135657227245)
                      ·
                        rfl

theorem cell23_4117331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 3, 1, 3, 6].length) (baseStart_4117331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4117331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4117331 prefixEnd_4117331 := by exact prefixLift 4117331
  have htrace : WordTrace (prefixWord ++ tailWord_4117331) baseStart_4117331 baseEnd_4117331 := by
    simpa [prefixWord, tailWord_4117331, baseEnd_4117331] using wordTrace_append hprefix tailTrace_4117331
  have hstable : (prefixWord ++ tailWord_4117331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4117331).length < 2 ^ (prefixWord ++ tailWord_4117331).sum := by decide
  have hdescent : baseEnd_4117331 < baseStart_4117331 := by decide
  rcases family_descends (prefixWord ++ tailWord_4117331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4117335 : List Nat := [1, 1, 3, 2, 4, 2, 1, 2, 2, 1, 4]
def baseStart_4117335 : Nat := 118140960795 + 4117335 * 2 ^ 59
def prefixEnd_4117335 : Nat := 4983230072969 + 3 ^ 40 * 4117335 * 2
def baseEnd_4117335 : Nat := 2114171870579753641577227

theorem tailTrace_4117335 : CollatzResearch.WordTrace tailWord_4117335 prefixEnd_4117335 2114171870579753641577227 := by
  unfold tailWord_4117335
  simp only [CollatzResearch.WordTrace]
  refine ⟨150171544538605954679705459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100114363025737303119803639 150171544538605954679705459)
  ·
    refine ⟨225257316807908932019558189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150171544538605954679705459 225257316807908932019558189)
    ·
      refine ⟨84471493802965849507334321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 225257316807908932019558189 84471493802965849507334321)
      ·
        refine ⟨63353620352224387130500741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84471493802965849507334321 63353620352224387130500741)
        ·
          refine ⟨11878803816042072586968889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 63353620352224387130500741 11878803816042072586968889)
          ·
            refine ⟨8909102862031554440226667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11878803816042072586968889 8909102862031554440226667)
            ·
              refine ⟨13363654293047331660340001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8909102862031554440226667 13363654293047331660340001)
              ·
                refine ⟨10022740719785498745255001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13363654293047331660340001 10022740719785498745255001)
                ·
                  refine ⟨7517055539839124058941251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10022740719785498745255001 7517055539839124058941251)
                  ·
                    refine ⟨11275583309758686088411877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7517055539839124058941251 11275583309758686088411877)
                    ·
                      refine ⟨2114171870579753641577227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11275583309758686088411877 2114171870579753641577227)
                      ·
                        rfl

theorem cell23_4117335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 1, 2, 2, 1, 4].length) (baseStart_4117335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4117335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4117335 prefixEnd_4117335 := by exact prefixLift 4117335
  have htrace : WordTrace (prefixWord ++ tailWord_4117335) baseStart_4117335 baseEnd_4117335 := by
    simpa [prefixWord, tailWord_4117335, baseEnd_4117335] using wordTrace_append hprefix tailTrace_4117335
  have hstable : (prefixWord ++ tailWord_4117335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4117335).length < 2 ^ (prefixWord ++ tailWord_4117335).sum := by decide
  have hdescent : baseEnd_4117335 < baseStart_4117335 := by decide
  rcases family_descends (prefixWord ++ tailWord_4117335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4117395 : List Nat := [1, 1, 1, 2, 1, 2, 1, 5, 4, 3, 2]
def baseStart_4117395 : Nat := 118140960795 + 4117395 * 2 ^ 59
def prefixEnd_4117395 : Nat := 4983230072969 + 3 ^ 40 * 4117395 * 2
def baseEnd_4117395 : Nat := 2114202679419023406826951

theorem tailTrace_4117395 : CollatzResearch.WordTrace tailWord_4117395 prefixEnd_4117395 2114202679419023406826951 := by
  unfold tailWord_4117395
  simp only [CollatzResearch.WordTrace]
  refine ⟨150173732918388584926889639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100115821945592389951259759 150173732918388584926889639)
  ·
    refine ⟨225260599377582877390334459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150173732918388584926889639 225260599377582877390334459)
    ·
      refine ⟨337890899066374316085501689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225260599377582877390334459 337890899066374316085501689)
      ·
        refine ⟨253418174299780737064126267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 337890899066374316085501689 253418174299780737064126267)
        ·
          refine ⟨380127261449671105596189401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 253418174299780737064126267 380127261449671105596189401)
          ·
            refine ⟨285095446087253329197142051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 380127261449671105596189401 285095446087253329197142051)
            ·
              refine ⟨427643169130879993795713077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 285095446087253329197142051 427643169130879993795713077)
              ·
                refine ⟨40091547106019999418348101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 427643169130879993795713077 40091547106019999418348101)
                ·
                  refine ⟨7517165082378749890940269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40091547106019999418348101 7517165082378749890940269)
                  ·
                    refine ⟨2818936905892031209102601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7517165082378749890940269 2818936905892031209102601)
                    ·
                      refine ⟨2114202679419023406826951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2818936905892031209102601 2114202679419023406826951)
                      ·
                        rfl

theorem cell23_4117395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 5, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 5, 4, 3, 2].length) (baseStart_4117395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4117395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4117395 prefixEnd_4117395 := by exact prefixLift 4117395
  have htrace : WordTrace (prefixWord ++ tailWord_4117395) baseStart_4117395 baseEnd_4117395 := by
    simpa [prefixWord, tailWord_4117395, baseEnd_4117395] using wordTrace_append hprefix tailTrace_4117395
  have hstable : (prefixWord ++ tailWord_4117395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4117395).length < 2 ^ (prefixWord ++ tailWord_4117395).sum := by decide
  have hdescent : baseEnd_4117395 < baseStart_4117395 := by decide
  rcases family_descends (prefixWord ++ tailWord_4117395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4117430 : List Nat := [5, 1, 4, 1, 1, 1, 2, 3, 1, 4]
def baseStart_4117430 : Nat := 118140960795 + 4117430 * 2 ^ 59
def prefixEnd_4117430 : Nat := 4983230072969 + 3 ^ 40 * 4117430 * 2
def baseEnd_4117430 : Nat := 704740217080643589963097

theorem tailTrace_4117430 : CollatzResearch.WordTrace tailWord_4117430 prefixEnd_4117430 704740217080643589963097 := by
  unfold tailWord_4117430
  simp only [CollatzResearch.WordTrace]
  refine ⟨9385938092078861619025859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 100116672982174523936275829 9385938092078861619025859)
  ·
    refine ⟨14078907138118292428538789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9385938092078861619025859 14078907138118292428538789)
    ·
      refine ⟨2639795088397179830351023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14078907138118292428538789 2639795088397179830351023)
      ·
        refine ⟨3959692632595769745526535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2639795088397179830351023 3959692632595769745526535)
        ·
          refine ⟨5939538948893654618289803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3959692632595769745526535 5939538948893654618289803)
          ·
            refine ⟨8909308423340481927434705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5939538948893654618289803 8909308423340481927434705)
            ·
              refine ⟨6681981317505361445576029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8909308423340481927434705 6681981317505361445576029)
              ·
                refine ⟨2505742994064510542091011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6681981317505361445576029 2505742994064510542091011)
                ·
                  refine ⟨3758614491096765813136517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2505742994064510542091011 3758614491096765813136517)
                  ·
                    refine ⟨704740217080643589963097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3758614491096765813136517 704740217080643589963097)
                    ·
                      rfl

theorem cell23_4117430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 2, 3, 1, 4].length) (baseStart_4117430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4117430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4117430 prefixEnd_4117430 := by exact prefixLift 4117430
  have htrace : WordTrace (prefixWord ++ tailWord_4117430) baseStart_4117430 baseEnd_4117430 := by
    simpa [prefixWord, tailWord_4117430, baseEnd_4117430] using wordTrace_append hprefix tailTrace_4117430
  have hstable : (prefixWord ++ tailWord_4117430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4117430).length < 2 ^ (prefixWord ++ tailWord_4117430).sum := by decide
  have hdescent : baseEnd_4117430 < baseStart_4117430 := by decide
  rcases family_descends (prefixWord ++ tailWord_4117430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4117462 : List Nat := [5, 2, 1, 1, 2, 1, 1, 1, 3, 1, 5]
def baseStart_4117462 : Nat := 118140960795 + 4117462 * 2 ^ 59
def prefixEnd_4117462 : Nat := 4983230072969 + 3 ^ 40 * 4117462 * 2
def baseEnd_4117462 : Nat := 2114237082622874644689143

theorem tailTrace_4117462 : CollatzResearch.WordTrace tailWord_4117462 prefixEnd_4117462 2114237082622874644689143 := by
  unfold tailWord_4117462
  simp only [CollatzResearch.WordTrace]
  refine ⟨9386011038071615960598665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 100117451072763903579719093 9386011038071615960598665)
  ·
    refine ⟨7039508278553711970448999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9386011038071615960598665 7039508278553711970448999)
    ·
      refine ⟨10559262417830567955673499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7039508278553711970448999 10559262417830567955673499)
      ·
        refine ⟨15838893626745851933510249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10559262417830567955673499 15838893626745851933510249)
        ·
          refine ⟨11879170220059388950132687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15838893626745851933510249 11879170220059388950132687)
          ·
            refine ⟨17818755330089083425199031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11879170220059388950132687 17818755330089083425199031)
            ·
              refine ⟨26728132995133625137798547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17818755330089083425199031 26728132995133625137798547)
              ·
                refine ⟨40092199492700437706697821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26728132995133625137798547 40092199492700437706697821)
                ·
                  refine ⟨15034574809762664140011683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40092199492700437706697821 15034574809762664140011683)
                  ·
                    refine ⟨22551862214643996210017525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15034574809762664140011683 22551862214643996210017525)
                    ·
                      refine ⟨2114237082622874644689143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22551862214643996210017525 2114237082622874644689143)
                      ·
                        rfl

theorem cell23_4117462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 1, 1, 3, 1, 5].length) (baseStart_4117462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4117462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4117462 prefixEnd_4117462 := by exact prefixLift 4117462
  have htrace : WordTrace (prefixWord ++ tailWord_4117462) baseStart_4117462 baseEnd_4117462 := by
    simpa [prefixWord, tailWord_4117462, baseEnd_4117462] using wordTrace_append hprefix tailTrace_4117462
  have hstable : (prefixWord ++ tailWord_4117462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4117462).length < 2 ^ (prefixWord ++ tailWord_4117462).sum := by decide
  have hdescent : baseEnd_4117462 < baseStart_4117462 := by decide
  rcases family_descends (prefixWord ++ tailWord_4117462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4117479 : List Nat := [1, 1, 5, 2, 2, 2, 2, 2, 1, 2, 3]
def baseStart_4117479 : Nat := 118140960795 + 4117479 * 2 ^ 59
def prefixEnd_4117479 : Nat := 4983230072969 + 3 ^ 40 * 4117479 * 2
def baseEnd_4117479 : Nat := 2114245811794001078176565

theorem tailTrace_4117479 : CollatzResearch.WordTrace tailWord_4117479 prefixEnd_4117479 2114245811794001078176565 := by
  unfold tailWord_4117479
  simp only [CollatzResearch.WordTrace]
  refine ⟨150176796650084267272947491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100117864433389511515298327 150176796650084267272947491)
  ·
    refine ⟨225265194975126400909421237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150176796650084267272947491 225265194975126400909421237)
    ·
      refine ⟨21118612028918100085258241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 225265194975126400909421237 21118612028918100085258241)
      ·
        refine ⟨15838959021688575063943681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21118612028918100085258241 15838959021688575063943681)
        ·
          refine ⟨11879219266266431297957761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15838959021688575063943681 11879219266266431297957761)
          ·
            refine ⟨8909414449699823473468321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11879219266266431297957761 8909414449699823473468321)
            ·
              refine ⟨6682060837274867605101241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8909414449699823473468321 6682060837274867605101241)
              ·
                refine ⟨5011545627956150703825931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6682060837274867605101241 5011545627956150703825931)
                ·
                  refine ⟨7517318441934226055738897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5011545627956150703825931 7517318441934226055738897)
                  ·
                    refine ⟨5637988831450669541804173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7517318441934226055738897 5637988831450669541804173)
                    ·
                      refine ⟨2114245811794001078176565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5637988831450669541804173 2114245811794001078176565)
                      ·
                        rfl

theorem cell23_4117479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 2, 2, 1, 2, 3].length) (baseStart_4117479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4117479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4117479 prefixEnd_4117479 := by exact prefixLift 4117479
  have htrace : WordTrace (prefixWord ++ tailWord_4117479) baseStart_4117479 baseEnd_4117479 := by
    simpa [prefixWord, tailWord_4117479, baseEnd_4117479] using wordTrace_append hprefix tailTrace_4117479
  have hstable : (prefixWord ++ tailWord_4117479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4117479).length < 2 ^ (prefixWord ++ tailWord_4117479).sum := by decide
  have hdescent : baseEnd_4117479 < baseStart_4117479 := by decide
  rcases family_descends (prefixWord ++ tailWord_4117479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4117482 : List Nat := [3, 1, 3, 1, 2, 4, 2, 7]
def baseStart_4117482 : Nat := 118140960795 + 4117482 * 2 ^ 59
def prefixEnd_4117482 : Nat := 4983230072969 + 3 ^ 40 * 4117482 * 2
def baseEnd_4117482 : Nat := 78305457490220909868113

theorem tailTrace_4117482 : CollatzResearch.WordTrace tailWord_4117482 prefixEnd_4117482 78305457490220909868113 := by
  unfold tailWord_4117482
  simp only [CollatzResearch.WordTrace]
  refine ⟨37544226517268349696326675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100117937379382265856871133 37544226517268349696326675)
  ·
    refine ⟨56316339775902524544490013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37544226517268349696326675 56316339775902524544490013)
    ·
      refine ⟨21118627415963446704183755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56316339775902524544490013 21118627415963446704183755)
      ·
        refine ⟨31677941123945170056275633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21118627415963446704183755 31677941123945170056275633)
        ·
          refine ⟨23758455842958877542206725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31677941123945170056275633 23758455842958877542206725)
          ·
            refine ⟨4454710470554789539163761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23758455842958877542206725 4454710470554789539163761)
            ·
              refine ⟨3341032852916092154372821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4454710470554789539163761 3341032852916092154372821)
              ·
                refine ⟨78305457490220909868113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3341032852916092154372821 78305457490220909868113)
                ·
                  rfl

theorem cell23_4117482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 4, 2, 7].length) (baseStart_4117482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4117482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4117482 prefixEnd_4117482 := by exact prefixLift 4117482
  have htrace : WordTrace (prefixWord ++ tailWord_4117482) baseStart_4117482 baseEnd_4117482 := by
    simpa [prefixWord, tailWord_4117482, baseEnd_4117482] using wordTrace_append hprefix tailTrace_4117482
  have hstable : (prefixWord ++ tailWord_4117482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4117482).length < 2 ^ (prefixWord ++ tailWord_4117482).sum := by decide
  have hdescent : baseEnd_4117482 < baseStart_4117482 := by decide
  rcases family_descends (prefixWord ++ tailWord_4117482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4117498 : List Nat := [3, 1, 1, 1, 1, 2, 1, 2, 1, 2, 8]
def baseStart_4117498 : Nat := 118140960795 + 4117498 * 2 ^ 59
def prefixEnd_4117498 : Nat := 4983230072969 + 3 ^ 40 * 4117498 * 2
def baseEnd_4117498 : Nat := 2114255567926436503838977

theorem tailTrace_4117498 : CollatzResearch.WordTrace tailWord_4117498 prefixEnd_4117498 2114255567926436503838977 := by
  unfold tailWord_4117498
  simp only [CollatzResearch.WordTrace]
  refine ⟨37544372409253858379472287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100118326424676955678592765 37544372409253858379472287)
  ·
    refine ⟨56316558613880787569208431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37544372409253858379472287 56316558613880787569208431)
    ·
      refine ⟨84474837920821181353812647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56316558613880787569208431 84474837920821181353812647)
      ·
        refine ⟨126712256881231772030718971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84474837920821181353812647 126712256881231772030718971)
        ·
          refine ⟨190068385321847658046078457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126712256881231772030718971 190068385321847658046078457)
          ·
            refine ⟨142551288991385743534558843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 190068385321847658046078457 142551288991385743534558843)
            ·
              refine ⟨213826933487078615301838265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 142551288991385743534558843 213826933487078615301838265)
              ·
                refine ⟨160370200115308961476378699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 213826933487078615301838265 160370200115308961476378699)
                ·
                  refine ⟨240555300172963442214568049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 160370200115308961476378699 240555300172963442214568049)
                  ·
                    refine ⟨180416475129722581660926037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 240555300172963442214568049 180416475129722581660926037)
                    ·
                      refine ⟨2114255567926436503838977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 180416475129722581660926037 2114255567926436503838977)
                      ·
                        rfl

theorem cell23_4117498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 2, 1, 2, 8].length) (baseStart_4117498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4117498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4117498 prefixEnd_4117498 := by exact prefixLift 4117498
  have htrace : WordTrace (prefixWord ++ tailWord_4117498) baseStart_4117498 baseEnd_4117498 := by
    simpa [prefixWord, tailWord_4117498, baseEnd_4117498] using wordTrace_append hprefix tailTrace_4117498
  have hstable : (prefixWord ++ tailWord_4117498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4117498).length < 2 ^ (prefixWord ++ tailWord_4117498).sum := by decide
  have hdescent : baseEnd_4117498 < baseStart_4117498 := by decide
  rcases family_descends (prefixWord ++ tailWord_4117498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4117535 : List Nat := [1, 1, 2, 4, 1, 3, 1, 2, 2, 1, 5]
def baseStart_4117535 : Nat := 118140960795 + 4117535 * 2 ^ 59
def prefixEnd_4117535 : Nat := 4983230072969 + 3 ^ 40 * 4117535 * 2
def baseEnd_4117535 : Nat := 2114274566710652859076307

theorem tailTrace_4117535 : CollatzResearch.WordTrace tailWord_4117535 prefixEnd_4117535 2114274566710652859076307 := by
  unfold tailWord_4117535
  simp only [CollatzResearch.WordTrace]
  refine ⟨150178839137881388836986059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100119226091920925891324039 150178839137881388836986059)
  ·
    refine ⟨225268258706822083255479089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150178839137881388836986059 225268258706822083255479089)
    ·
      refine ⟨168951194030116562441609317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 225268258706822083255479089 168951194030116562441609317)
      ·
        refine ⟨31678348880646855457801747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 168951194030116562441609317 31678348880646855457801747)
        ·
          refine ⟨47517523320970283186702621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31678348880646855457801747 47517523320970283186702621)
          ·
            refine ⟨17819071245363856195013483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47517523320970283186702621 17819071245363856195013483)
            ·
              refine ⟨26728606868045784292520225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17819071245363856195013483 26728606868045784292520225)
              ·
                refine ⟨20046455151034338219390169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26728606868045784292520225 20046455151034338219390169)
                ·
                  refine ⟨15034841363275753664542627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20046455151034338219390169 15034841363275753664542627)
                  ·
                    refine ⟨22552262044913630496813941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15034841363275753664542627 22552262044913630496813941)
                    ·
                      refine ⟨2114274566710652859076307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22552262044913630496813941 2114274566710652859076307)
                      ·
                        rfl

theorem cell23_4117535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 1, 2, 2, 1, 5].length) (baseStart_4117535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4117535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4117535 prefixEnd_4117535 := by exact prefixLift 4117535
  have htrace : WordTrace (prefixWord ++ tailWord_4117535) baseStart_4117535 baseEnd_4117535 := by
    simpa [prefixWord, tailWord_4117535, baseEnd_4117535] using wordTrace_append hprefix tailTrace_4117535
  have hstable : (prefixWord ++ tailWord_4117535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4117535).length < 2 ^ (prefixWord ++ tailWord_4117535).sum := by decide
  have hdescent : baseEnd_4117535 < baseStart_4117535 := by decide
  rcases family_descends (prefixWord ++ tailWord_4117535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4117536 : List Nat := [2, 1, 1, 7, 1, 1, 1, 1, 3, 3, 2]
def baseStart_4117536 : Nat := 118140960795 + 4117536 * 2 ^ 59
def prefixEnd_4117536 : Nat := 4983230072969 + 3 ^ 40 * 4117536 * 2
def baseEnd_4117536 : Nat := 2114275080191307355163803

theorem tailTrace_4117536 : CollatzResearch.WordTrace tailWord_4117536 prefixEnd_4117536 2114275080191307355163803 := by
  unfold tailWord_4117536
  simp only [CollatzResearch.WordTrace]
  refine ⟨75089437805438883003886231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100119250407251844005181641 75089437805438883003886231)
  ·
    refine ⟨112634156708158324505829347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75089437805438883003886231 112634156708158324505829347)
    ·
      refine ⟨168951235062237486758744021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112634156708158324505829347 168951235062237486758744021)
      ·
        refine ⟨3959794571771191095908063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 168951235062237486758744021 3959794571771191095908063)
        ·
          refine ⟨5939691857656786643862095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3959794571771191095908063 5939691857656786643862095)
          ·
            refine ⟨8909537786485179965793143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5939691857656786643862095 8909537786485179965793143)
            ·
              refine ⟨13364306679727769948689715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8909537786485179965793143 13364306679727769948689715)
              ·
                refine ⟨20046460019591654923034573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13364306679727769948689715 20046460019591654923034573)
                ·
                  refine ⟨7517422507346870596137965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20046460019591654923034573 7517422507346870596137965)
                  ·
                    refine ⟨2819033440255076473551737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7517422507346870596137965 2819033440255076473551737)
                    ·
                      refine ⟨2114275080191307355163803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2819033440255076473551737 2114275080191307355163803)
                      ·
                        rfl

theorem cell23_4117536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 1, 1, 3, 3, 2].length) (baseStart_4117536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4117536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4117536 prefixEnd_4117536 := by exact prefixLift 4117536
  have htrace : WordTrace (prefixWord ++ tailWord_4117536) baseStart_4117536 baseEnd_4117536 := by
    simpa [prefixWord, tailWord_4117536, baseEnd_4117536] using wordTrace_append hprefix tailTrace_4117536
  have hstable : (prefixWord ++ tailWord_4117536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4117536).length < 2 ^ (prefixWord ++ tailWord_4117536).sum := by decide
  have hdescent : baseEnd_4117536 < baseStart_4117536 := by decide
  rcases family_descends (prefixWord ++ tailWord_4117536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4117582 : List Nat := [4, 1, 1, 1, 1, 3, 3, 1, 2, 3, 3]
def baseStart_4117582 : Nat := 118140960795 + 4117582 * 2 ^ 59
def prefixEnd_4117582 : Nat := 4983230072969 + 3 ^ 40 * 4117582 * 2
def baseEnd_4117582 : Nat := 2114298700301414175188591

theorem tailTrace_4117582 : CollatzResearch.WordTrace tailWord_4117582 prefixEnd_4117582 2114298700301414175188591 := by
  unfold tailWord_4117582
  simp only [CollatzResearch.WordTrace]
  refine ⟨18772569171088889482993375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 100120368912474077242631333 18772569171088889482993375)
  ·
    refine ⟨28158853756633334224490063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18772569171088889482993375 28158853756633334224490063)
    ·
      refine ⟨42238280634950001336735095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28158853756633334224490063 42238280634950001336735095)
      ·
        refine ⟨63357420952425002005102643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42238280634950001336735095 63357420952425002005102643)
        ·
          refine ⟨95036131428637503007653965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63357420952425002005102643 95036131428637503007653965)
          ·
            refine ⟨35638549285739063627870237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 95036131428637503007653965 35638549285739063627870237)
            ·
              refine ⟨13364455982152148860451339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35638549285739063627870237 13364455982152148860451339)
              ·
                refine ⟨20046683973228223290677009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13364455982152148860451339 20046683973228223290677009)
                ·
                  refine ⟨15035012979921167468007757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20046683973228223290677009 15035012979921167468007757)
                  ·
                    refine ⟨5638129867470437800502909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15035012979921167468007757 5638129867470437800502909)
                    ·
                      refine ⟨2114298700301414175188591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5638129867470437800502909 2114298700301414175188591)
                      ·
                        rfl

theorem cell23_4117582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 3, 1, 2, 3, 3].length) (baseStart_4117582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4117582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4117582 prefixEnd_4117582 := by exact prefixLift 4117582
  have htrace : WordTrace (prefixWord ++ tailWord_4117582) baseStart_4117582 baseEnd_4117582 := by
    simpa [prefixWord, tailWord_4117582, baseEnd_4117582] using wordTrace_append hprefix tailTrace_4117582
  have hstable : (prefixWord ++ tailWord_4117582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4117582).length < 2 ^ (prefixWord ++ tailWord_4117582).sum := by decide
  have hdescent : baseEnd_4117582 < baseStart_4117582 := by decide
  rcases family_descends (prefixWord ++ tailWord_4117582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4117585 : List Nat := [1, 2, 2, 1, 3, 1, 2, 2, 4, 5]
def baseStart_4117585 : Nat := 118140960795 + 4117585 * 2 ^ 59
def prefixEnd_4117585 : Nat := 4983230072969 + 3 ^ 40 * 4117585 * 2
def baseEnd_4117585 : Nat := 704766746914459221150359

theorem tailTrace_4117585 : CollatzResearch.WordTrace tailWord_4117585 prefixEnd_4117585 704766746914459221150359 := by
  unfold tailWord_4117585
  simp only [CollatzResearch.WordTrace]
  refine ⟨150180662787700247376306209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100120441858466831584204139 150180662787700247376306209)
  ·
    refine ⟨112635497090775185532229657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150180662787700247376306209 112635497090775185532229657)
    ·
      refine ⟨84476622818081389149172243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112635497090775185532229657 84476622818081389149172243)
      ·
        refine ⟨126714934227122083723758365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84476622818081389149172243 126714934227122083723758365)
        ·
          refine ⟨47518100335170781396409387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 126714934227122083723758365 47518100335170781396409387)
          ·
            refine ⟨71277150502756172094614081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47518100335170781396409387 71277150502756172094614081)
            ·
              refine ⟨53457862877067129070960561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71277150502756172094614081 53457862877067129070960561)
              ·
                refine ⟨40093397157800346803220421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53457862877067129070960561 40093397157800346803220421)
                ·
                  refine ⟨7517511967087565025603829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40093397157800346803220421 7517511967087565025603829)
                  ·
                    refine ⟨704766746914459221150359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7517511967087565025603829 704766746914459221150359)
                    ·
                      rfl

theorem cell23_4117585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 2, 4, 5].length) (baseStart_4117585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4117585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4117585 prefixEnd_4117585 := by exact prefixLift 4117585
  have htrace : WordTrace (prefixWord ++ tailWord_4117585) baseStart_4117585 baseEnd_4117585 := by
    simpa [prefixWord, tailWord_4117585, baseEnd_4117585] using wordTrace_append hprefix tailTrace_4117585
  have hstable : (prefixWord ++ tailWord_4117585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4117585).length < 2 ^ (prefixWord ++ tailWord_4117585).sum := by decide
  have hdescent : baseEnd_4117585 < baseStart_4117585 := by decide
  rcases family_descends (prefixWord ++ tailWord_4117585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4117592 : List Nat := [2, 1, 2, 2, 1, 3, 1, 2, 2, 5, 2]
def baseStart_4117592 : Nat := 118140960795 + 4117592 * 2 ^ 59
def prefixEnd_4117592 : Nat := 4983230072969 + 3 ^ 40 * 4117592 * 2
def baseEnd_4117592 : Nat := 2114303835107959136063545

theorem tailTrace_4117592 : CollatzResearch.WordTrace tailWord_4117592 prefixEnd_4117592 2114303835107959136063545 := by
  unfold tailWord_4117592
  simp only [CollatzResearch.WordTrace]
  refine ⟨75090459049337443785905515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100120612065783258381207353 75090459049337443785905515)
  ·
    refine ⟨112635688574006165678858273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75090459049337443785905515 112635688574006165678858273)
    ·
      refine ⟨84476766430504624259143705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112635688574006165678858273 84476766430504624259143705)
      ·
        refine ⟨63357574822878468194357779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84476766430504624259143705 63357574822878468194357779)
        ·
          refine ⟨95036362234317702291536669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63357574822878468194357779 95036362234317702291536669)
          ·
            refine ⟨35638635837869138359326251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 95036362234317702291536669 35638635837869138359326251)
            ·
              refine ⟨53457953756803707538989377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35638635837869138359326251 53457953756803707538989377)
              ·
                refine ⟨40093465317602780654242033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53457953756803707538989377 40093465317602780654242033)
                ·
                  refine ⟨30070098988202085490681525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40093465317602780654242033 30070098988202085490681525)
                  ·
                    refine ⟨2819071780143945514751393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 30070098988202085490681525 2819071780143945514751393)
                    ·
                      refine ⟨2114303835107959136063545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2819071780143945514751393 2114303835107959136063545)
                      ·
                        rfl

theorem cell23_4117592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 2, 2, 5, 2].length) (baseStart_4117592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4117592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4117592 prefixEnd_4117592 := by exact prefixLift 4117592
  have htrace : WordTrace (prefixWord ++ tailWord_4117592) baseStart_4117592 baseEnd_4117592 := by
    simpa [prefixWord, tailWord_4117592, baseEnd_4117592] using wordTrace_append hprefix tailTrace_4117592
  have hstable : (prefixWord ++ tailWord_4117592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4117592).length < 2 ^ (prefixWord ++ tailWord_4117592).sum := by decide
  have hdescent : baseEnd_4117592 < baseStart_4117592 := by decide
  rcases family_descends (prefixWord ++ tailWord_4117592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4117632 : List Nat := [2, 1, 1, 2, 1, 3, 3, 3, 3, 4]
def baseStart_4117632 : Nat := 118140960795 + 4117632 * 2 ^ 59
def prefixEnd_4117632 : Nat := 4983230072969 + 3 ^ 40 * 4117632 * 2
def baseEnd_4117632 : Nat := 704774791444712993187787

theorem tailTrace_4117632 : CollatzResearch.WordTrace tailWord_4117632 prefixEnd_4117632 704774791444712993187787 := by
  unfold tailWord_4117632
  simp only [CollatzResearch.WordTrace]
  refine ⟨75091188509264987201633575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100121584679019982935511433 75091188509264987201633575)
  ·
    refine ⟨112636782763897480802450363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75091188509264987201633575 112636782763897480802450363)
    ·
      refine ⟨168955174145846221203675545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112636782763897480802450363 168955174145846221203675545)
      ·
        refine ⟨126716380609384665902756659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 168955174145846221203675545 126716380609384665902756659)
        ·
          refine ⟨190074570914076998854134989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126716380609384665902756659 190074570914076998854134989)
          ·
            refine ⟨71277964092778874570300621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 190074570914076998854134989 71277964092778874570300621)
            ·
              refine ⟨26729236534792077963862733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71277964092778874570300621 26729236534792077963862733)
              ·
                refine ⟨10023463700547029236448525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26729236534792077963862733 10023463700547029236448525)
                ·
                  refine ⟨3758798887705135963668197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10023463700547029236448525 3758798887705135963668197)
                  ·
                    refine ⟨704774791444712993187787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3758798887705135963668197 704774791444712993187787)
                    ·
                      rfl

theorem cell23_4117632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 3, 3, 3, 4].length) (baseStart_4117632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4117632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4117632 prefixEnd_4117632 := by exact prefixLift 4117632
  have htrace : WordTrace (prefixWord ++ tailWord_4117632) baseStart_4117632 baseEnd_4117632 := by
    simpa [prefixWord, tailWord_4117632, baseEnd_4117632] using wordTrace_append hprefix tailTrace_4117632
  have hstable : (prefixWord ++ tailWord_4117632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4117632).length < 2 ^ (prefixWord ++ tailWord_4117632).sum := by decide
  have hdescent : baseEnd_4117632 < baseStart_4117632 := by decide
  rcases family_descends (prefixWord ++ tailWord_4117632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4117635 : List Nat := [1, 1, 1, 3, 3, 2, 1, 2, 2, 1, 6]
def baseStart_4117635 : Nat := 118140960795 + 4117635 * 2 ^ 59
def prefixEnd_4117635 : Nat := 4983230072969 + 3 ^ 40 * 4117635 * 2
def baseEnd_4117635 : Nat := 2114325914776102467825847

theorem tailTrace_4117635 : CollatzResearch.WordTrace tailWord_4117635 prefixEnd_4117635 2114325914776102467825847 := by
  unfold tailWord_4117635
  simp only [CollatzResearch.WordTrace]
  refine ⟨150182486437519105915626359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100121657625012737277084239 150182486437519105915626359)
  ·
    refine ⟨225273729656278658873439539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150182486437519105915626359 225273729656278658873439539)
    ·
      refine ⟨337910594484417988310159309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225273729656278658873439539 337910594484417988310159309)
      ·
        refine ⟨126716472931656745616309741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 337910594484417988310159309 126716472931656745616309741)
        ·
          refine ⟨47518677349371279606116153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 126716472931656745616309741 47518677349371279606116153)
          ·
            refine ⟨35639008012028459704587115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47518677349371279606116153 35639008012028459704587115)
            ·
              refine ⟨53458512018042689556880673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35639008012028459704587115 53458512018042689556880673)
              ·
                refine ⟨40093884013532017167660505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53458512018042689556880673 40093884013532017167660505)
                ·
                  refine ⟨30070413010149012875745379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40093884013532017167660505 30070413010149012875745379)
                  ·
                    refine ⟨45105619515223519313618069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30070413010149012875745379 45105619515223519313618069)
                    ·
                      refine ⟨2114325914776102467825847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 45105619515223519313618069 2114325914776102467825847)
                      ·
                        rfl

theorem cell23_4117635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 2, 2, 1, 6].length) (baseStart_4117635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4117635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4117635 prefixEnd_4117635 := by exact prefixLift 4117635
  have htrace : WordTrace (prefixWord ++ tailWord_4117635) baseStart_4117635 baseEnd_4117635 := by
    simpa [prefixWord, tailWord_4117635, baseEnd_4117635] using wordTrace_append hprefix tailTrace_4117635
  have hstable : (prefixWord ++ tailWord_4117635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4117635).length < 2 ^ (prefixWord ++ tailWord_4117635).sum := by decide
  have hdescent : baseEnd_4117635 < baseStart_4117635 := by decide
  rcases family_descends (prefixWord ++ tailWord_4117635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4117642 : List Nat := [3, 1, 2, 3, 1, 1, 1, 1, 3, 4, 3]
def baseStart_4117642 : Nat := 118140960795 + 4117642 * 2 ^ 59
def prefixEnd_4117642 : Nat := 4983230072969 + 3 ^ 40 * 4117642 * 2
def baseEnd_4117642 : Nat := 2114329509140683940438315

theorem tailTrace_4117642 : CollatzResearch.WordTrace tailWord_4117642 prefixEnd_4117642 2114329509140683940438315 := by
  unfold tailWord_4117642
  simp only [CollatzResearch.WordTrace]
  refine ⟨37545685437123436527782795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100121827832329164074087453 37545685437123436527782795)
  ·
    refine ⟨56318528155685154791674193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37545685437123436527782795 56318528155685154791674193)
    ·
      refine ⟨42238896116763866093755645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56318528155685154791674193 42238896116763866093755645)
      ·
        refine ⟨15839586043786449785158367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42238896116763866093755645 15839586043786449785158367)
        ·
          refine ⟨23759379065679674677737551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15839586043786449785158367 23759379065679674677737551)
          ·
            refine ⟨35639068598519512016606327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23759379065679674677737551 35639068598519512016606327)
            ·
              refine ⟨53458602897779268024909491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35639068598519512016606327 53458602897779268024909491)
              ·
                refine ⟨80187904346668902037364237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53458602897779268024909491 80187904346668902037364237)
                ·
                  refine ⟨30070464130000838264011589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 80187904346668902037364237 30070464130000838264011589)
                  ·
                    refine ⟨5638212024375157174502173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30070464130000838264011589 5638212024375157174502173)
                    ·
                      refine ⟨2114329509140683940438315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5638212024375157174502173 2114329509140683940438315)
                      ·
                        rfl

theorem cell23_4117642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 1, 3, 4, 3].length) (baseStart_4117642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4117642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4117642 prefixEnd_4117642 := by exact prefixLift 4117642
  have htrace : WordTrace (prefixWord ++ tailWord_4117642) baseStart_4117642 baseEnd_4117642 := by
    simpa [prefixWord, tailWord_4117642, baseEnd_4117642] using wordTrace_append hprefix tailTrace_4117642
  have hstable : (prefixWord ++ tailWord_4117642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4117642).length < 2 ^ (prefixWord ++ tailWord_4117642).sum := by decide
  have hdescent : baseEnd_4117642 < baseStart_4117642 := by decide
  rcases family_descends (prefixWord ++ tailWord_4117642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4117696 : List Nat := [2, 1, 1, 2, 6, 2, 2, 1, 6]
def baseStart_4117696 : Nat := 118140960795 + 4117696 * 2 ^ 59
def prefixEnd_4117696 : Nat := 4983230072969 + 3 ^ 40 * 4117696 * 2
def baseEnd_4117696 : Nat := 234928581899558525462563

theorem tailTrace_4117696 : CollatzResearch.WordTrace tailWord_4117696 prefixEnd_4117696 234928581899558525462563 := by
  unfold tailWord_4117696
  simp only [CollatzResearch.WordTrace]
  refine ⟨75092355645149056666798471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100123140860198742222397961 75092355645149056666798471)
  ·
    refine ⟨112638533467723585000197707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75092355645149056666798471 112638533467723585000197707)
    ·
      refine ⟨168957800201585377500296561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112638533467723585000197707 168957800201585377500296561)
      ·
        refine ⟨126718350151189033125222421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 168957800201585377500296561 126718350151189033125222421)
        ·
          refine ⟨5939922663336985927744801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 126718350151189033125222421 5939922663336985927744801)
          ·
            refine ⟨4454941997502739445808601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5939922663336985927744801 4454941997502739445808601)
            ·
              refine ⟨3341206498127054584356451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4454941997502739445808601 3341206498127054584356451)
              ·
                refine ⟨5011809747190581876534677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3341206498127054584356451 5011809747190581876534677)
                ·
                  refine ⟨234928581899558525462563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5011809747190581876534677 234928581899558525462563)
                  ·
                    rfl

theorem cell23_4117696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 2, 2, 1, 6].length) (baseStart_4117696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4117696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4117696 prefixEnd_4117696 := by exact prefixLift 4117696
  have htrace : WordTrace (prefixWord ++ tailWord_4117696) baseStart_4117696 baseEnd_4117696 := by
    simpa [prefixWord, tailWord_4117696, baseEnd_4117696] using wordTrace_append hprefix tailTrace_4117696
  have hstable : (prefixWord ++ tailWord_4117696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4117696).length < 2 ^ (prefixWord ++ tailWord_4117696).sum := by decide
  have hdescent : baseEnd_4117696 < baseStart_4117696 := by decide
  rcases family_descends (prefixWord ++ tailWord_4117696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4117739 : List Nat := [1, 1, 1, 1, 2, 6, 1, 4, 2, 4]
def baseStart_4117739 : Nat := 118140960795 + 4117739 * 2 ^ 59
def prefixEnd_4117739 : Nat := 4983230072969 + 3 ^ 40 * 4117739 * 2
def baseEnd_4117739 : Nat := 704793105588056686975123

theorem tailTrace_4117739 : CollatzResearch.WordTrace tailWord_4117739 prefixEnd_4117739 704793105588056686975123 := by
  unfold tailWord_4117739
  simp only [CollatzResearch.WordTrace]
  refine ⟨150186279629142331677412271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100124186419428221118274847 150186279629142331677412271)
  ·
    refine ⟨225279419443713497516118407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150186279629142331677412271 225279419443713497516118407)
    ·
      refine ⟨337919129165570246274177611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225279419443713497516118407 337919129165570246274177611)
      ·
        refine ⟨506878693748355369411266417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 337919129165570246274177611 506878693748355369411266417)
        ·
          refine ⟨380159020311266527058449813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 506878693748355369411266417 380159020311266527058449813)
          ·
            refine ⟨17819954077090618455864835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 380159020311266527058449813 17819954077090618455864835)
            ·
              refine ⟨26729931115635927683797253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17819954077090618455864835 26729931115635927683797253)
              ·
                refine ⟨5011862084181736440711985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26729931115635927683797253 5011862084181736440711985)
                ·
                  refine ⟨3758896563136302330533989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5011862084181736440711985 3758896563136302330533989)
                  ·
                    refine ⟨704793105588056686975123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3758896563136302330533989 704793105588056686975123)
                    ·
                      rfl

theorem cell23_4117739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 1, 4, 2, 4].length) (baseStart_4117739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4117739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4117739 prefixEnd_4117739 := by exact prefixLift 4117739
  have htrace : WordTrace (prefixWord ++ tailWord_4117739) baseStart_4117739 baseEnd_4117739 := by
    simpa [prefixWord, tailWord_4117739, baseEnd_4117739] using wordTrace_append hprefix tailTrace_4117739
  have hstable : (prefixWord ++ tailWord_4117739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4117739).length < 2 ^ (prefixWord ++ tailWord_4117739).sum := by decide
  have hdescent : baseEnd_4117739 < baseStart_4117739 := by decide
  rcases family_descends (prefixWord ++ tailWord_4117739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4117740 : List Nat := [2, 2, 1, 1, 2, 6, 2, 2, 1, 1, 3]
def baseStart_4117740 : Nat := 118140960795 + 4117740 * 2 ^ 59
def prefixEnd_4117740 : Nat := 4983230072969 + 3 ^ 40 * 4117740 * 2
def baseEnd_4117740 : Nat := 2114379830244824557012865

theorem tailTrace_4117740 : CollatzResearch.WordTrace tailWord_4117740 prefixEnd_4117740 2114379830244824557012865 := by
  unfold tailWord_4117740
  simp only [CollatzResearch.WordTrace]
  refine ⟨75093158051069354424099337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100124210734759139232132449 75093158051069354424099337)
  ·
    refine ⟨56319868538302015818074503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75093158051069354424099337 56319868538302015818074503)
    ·
      refine ⟨84479802807453023727111755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56319868538302015818074503 84479802807453023727111755)
      ·
        refine ⟨126719704211179535590667633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84479802807453023727111755 126719704211179535590667633)
        ·
          refine ⟨95039778158384651693000725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126719704211179535590667633 95039778158384651693000725)
          ·
            refine ⟨4454989601174280548109409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 95039778158384651693000725 4454989601174280548109409)
            ·
              refine ⟨3341242200880710411082057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4454989601174280548109409 3341242200880710411082057)
              ·
                refine ⟨2505931650660532808311543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3341242200880710411082057 2505931650660532808311543)
                ·
                  refine ⟨3758897475990799212467315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2505931650660532808311543 3758897475990799212467315)
                  ·
                    refine ⟨5638346213986198818700973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3758897475990799212467315 5638346213986198818700973)
                    ·
                      refine ⟨2114379830244824557012865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5638346213986198818700973 2114379830244824557012865)
                      ·
                        rfl

theorem cell23_4117740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 6, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 6, 2, 2, 1, 1, 3].length) (baseStart_4117740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4117740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4117740 prefixEnd_4117740 := by exact prefixLift 4117740
  have htrace : WordTrace (prefixWord ++ tailWord_4117740) baseStart_4117740 baseEnd_4117740 := by
    simpa [prefixWord, tailWord_4117740, baseEnd_4117740] using wordTrace_append hprefix tailTrace_4117740
  have hstable : (prefixWord ++ tailWord_4117740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4117740).length < 2 ^ (prefixWord ++ tailWord_4117740).sum := by decide
  have hdescent : baseEnd_4117740 < baseStart_4117740 := by decide
  rcases family_descends (prefixWord ++ tailWord_4117740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4117742 : List Nat := [4, 1, 2, 1, 1, 1, 2, 1, 3, 1, 6]
def baseStart_4117742 : Nat := 118140960795 + 4117742 * 2 ^ 59
def prefixEnd_4117742 : Nat := 4983230072969 + 3 ^ 40 * 4117742 * 2
def baseEnd_4117742 : Nat := 2114380857206133549187855

theorem tailTrace_4117742 : CollatzResearch.WordTrace tailWord_4117742 prefixEnd_4117742 2114380857206133549187855 := by
  unfold tailWord_4117742
  simp only [CollatzResearch.WordTrace]
  refine ⟨18773298631016432898721435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 100124259365420975459847653 18773298631016432898721435)
  ·
    refine ⟨28159947946524649348082153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18773298631016432898721435 28159947946524649348082153)
    ·
      refine ⟨21119960959893487011061615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28159947946524649348082153 21119960959893487011061615)
      ·
        refine ⟨31679941439840230516592423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21119960959893487011061615 31679941439840230516592423)
        ·
          refine ⟨47519912159760345774888635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31679941439840230516592423 47519912159760345774888635)
          ·
            refine ⟨71279868239640518662332953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47519912159760345774888635 71279868239640518662332953)
            ·
              refine ⟨53459901179730388996749715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71279868239640518662332953 53459901179730388996749715)
              ·
                refine ⟨80189851769595583495124573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53459901179730388996749715 80189851769595583495124573)
                ·
                  refine ⟨30071194413598343810671715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 80189851769595583495124573 30071194413598343810671715)
                  ·
                    refine ⟨45106791620397515716007573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30071194413598343810671715 45106791620397515716007573)
                    ·
                      refine ⟨2114380857206133549187855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 45106791620397515716007573 2114380857206133549187855)
                      ·
                        rfl

theorem cell23_4117742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 1, 3, 1, 6].length) (baseStart_4117742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4117742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4117742 prefixEnd_4117742 := by exact prefixLift 4117742
  have htrace : WordTrace (prefixWord ++ tailWord_4117742) baseStart_4117742 baseEnd_4117742 := by
    simpa [prefixWord, tailWord_4117742, baseEnd_4117742] using wordTrace_append hprefix tailTrace_4117742
  have hstable : (prefixWord ++ tailWord_4117742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4117742).length < 2 ^ (prefixWord ++ tailWord_4117742).sum := by decide
  have hdescent : baseEnd_4117742 < baseStart_4117742 := by decide
  rcases family_descends (prefixWord ++ tailWord_4117742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4117759 : List Nat := [1, 1, 2, 2, 1, 6, 2, 1, 1, 2, 4]
def baseStart_4117759 : Nat := 118140960795 + 4117759 * 2 ^ 59
def prefixEnd_4117759 : Nat := 4983230072969 + 3 ^ 40 * 4117759 * 2
def baseEnd_4117759 : Nat := 2114389586377259982675277

theorem tailTrace_4117759 : CollatzResearch.WordTrace tailWord_4117759 prefixEnd_4117759 2114389586377259982675277 := by
  unfold tailWord_4117759
  simp only [CollatzResearch.WordTrace]
  refine ⟨150187009089069875093140331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100124672726046583395426887 150187009089069875093140331)
  ·
    refine ⟨225280513633604812639710497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150187009089069875093140331 225280513633604812639710497)
    ·
      refine ⟨168960385225203609479782873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 225280513633604812639710497 168960385225203609479782873)
      ·
        refine ⟨126720288918902707109837155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 168960385225203609479782873 126720288918902707109837155)
        ·
          refine ⟨190080433378354060664755733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126720288918902707109837155 190080433378354060664755733)
          ·
            refine ⟨8910020314610346593660425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 190080433378354060664755733 8910020314610346593660425)
            ·
              refine ⟨6682515235957759945245319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8910020314610346593660425 6682515235957759945245319)
              ·
                refine ⟨10023772853936639917867979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6682515235957759945245319 10023772853936639917867979)
                ·
                  refine ⟨15035659280904959876801969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10023772853936639917867979 15035659280904959876801969)
                  ·
                    refine ⟨11276744460678719907601477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15035659280904959876801969 11276744460678719907601477)
                    ·
                      refine ⟨2114389586377259982675277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11276744460678719907601477 2114389586377259982675277)
                      ·
                        rfl

theorem cell23_4117759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 2, 1, 1, 2, 4].length) (baseStart_4117759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4117759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4117759 prefixEnd_4117759 := by exact prefixLift 4117759
  have htrace : WordTrace (prefixWord ++ tailWord_4117759) baseStart_4117759 baseEnd_4117759 := by
    simpa [prefixWord, tailWord_4117759, baseEnd_4117759] using wordTrace_append hprefix tailTrace_4117759
  have hstable : (prefixWord ++ tailWord_4117759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4117759).length < 2 ^ (prefixWord ++ tailWord_4117759).sum := by decide
  have hdescent : baseEnd_4117759 < baseStart_4117759 := by decide
  rcases family_descends (prefixWord ++ tailWord_4117759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4117796 : List Nat := [2, 3, 1, 3, 1, 1, 3, 1, 4, 1, 3]
def baseStart_4117796 : Nat := 118140960795 + 4117796 * 2 ^ 59
def prefixEnd_4117796 : Nat := 4983230072969 + 3 ^ 40 * 4117796 * 2
def baseEnd_4117796 : Nat := 2114408585161476337912607

theorem tailTrace_4117796 : CollatzResearch.WordTrace tailWord_4117796 prefixEnd_4117796 2114408585161476337912607 := by
  unfold tailWord_4117796
  simp only [CollatzResearch.WordTrace]
  refine ⟨75094179294967915206118621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100125572393290553608158161 75094179294967915206118621)
  ·
    refine ⟨28160317235612968202294483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75094179294967915206118621 28160317235612968202294483)
    ·
      refine ⟨42240475853419452303441725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28160317235612968202294483 42240475853419452303441725)
      ·
        refine ⟨15840178445032294613790647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42240475853419452303441725 15840178445032294613790647)
        ·
          refine ⟨23760267667548441920685971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15840178445032294613790647 23760267667548441920685971)
          ·
            refine ⟨35640401501322662881028957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23760267667548441920685971 35640401501322662881028957)
            ·
              refine ⟨13365150562995998580385859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35640401501322662881028957 13365150562995998580385859)
              ·
                refine ⟨20047725844493997870578789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13365150562995998580385859 20047725844493997870578789)
                ·
                  refine ⟨3758948595842624600733523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20047725844493997870578789 3758948595842624600733523)
                  ·
                    refine ⟨5638422893763936901100285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3758948595842624600733523 5638422893763936901100285)
                    ·
                      refine ⟨2114408585161476337912607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5638422893763936901100285 2114408585161476337912607)
                      ·
                        rfl

theorem cell23_4117796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 3, 1, 4, 1, 3].length) (baseStart_4117796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4117796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4117796 prefixEnd_4117796 := by exact prefixLift 4117796
  have htrace : WordTrace (prefixWord ++ tailWord_4117796) baseStart_4117796 baseEnd_4117796 := by
    simpa [prefixWord, tailWord_4117796, baseEnd_4117796] using wordTrace_append hprefix tailTrace_4117796
  have hstable : (prefixWord ++ tailWord_4117796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4117796).length < 2 ^ (prefixWord ++ tailWord_4117796).sum := by decide
  have hdescent : baseEnd_4117796 < baseStart_4117796 := by decide
  rcases family_descends (prefixWord ++ tailWord_4117796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4117823 : List Nat := [1, 1, 2, 2, 4, 3, 2, 2, 1, 3, 2]
def baseStart_4117823 : Nat := 118140960795 + 4117823 * 2 ^ 59
def prefixEnd_4117823 : Nat := 4983230072969 + 3 ^ 40 * 4117823 * 2
def baseEnd_4117823 : Nat := 2114422449139147732274983

theorem tailTrace_4117823 : CollatzResearch.WordTrace tailWord_4117823 prefixEnd_4117823 2114422449139147732274983 := by
  unfold tailWord_4117823
  simp only [CollatzResearch.WordTrace]
  refine ⟨150189343360838014023470123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100126228907225342682313415 150189343360838014023470123)
  ·
    refine ⟨225284015041257021035205185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150189343360838014023470123 225284015041257021035205185)
    ·
      refine ⟨168963011280942765776403889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 225284015041257021035205185 168963011280942765776403889)
      ·
        refine ⟨126722258460707074332302917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 168963011280942765776403889 126722258460707074332302917)
        ·
          refine ⟨23760423461382576437306797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 126722258460707074332302917 23760423461382576437306797)
          ·
            refine ⟨8910158798018466163990049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23760423461382576437306797 8910158798018466163990049)
            ·
              refine ⟨6682619098513849622992537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8910158798018466163990049 6682619098513849622992537)
              ·
                refine ⟨5011964323885387217244403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6682619098513849622992537 5011964323885387217244403)
                ·
                  refine ⟨7517946485828080825866605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5011964323885387217244403 7517946485828080825866605)
                  ·
                    refine ⟨2819229932185530309699977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7517946485828080825866605 2819229932185530309699977)
                    ·
                      refine ⟨2114422449139147732274983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2819229932185530309699977 2114422449139147732274983)
                      ·
                        rfl

theorem cell23_4117823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 2, 2, 1, 3, 2].length) (baseStart_4117823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4117823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4117823 prefixEnd_4117823 := by exact prefixLift 4117823
  have htrace : WordTrace (prefixWord ++ tailWord_4117823) baseStart_4117823 baseEnd_4117823 := by
    simpa [prefixWord, tailWord_4117823, baseEnd_4117823] using wordTrace_append hprefix tailTrace_4117823
  have hstable : (prefixWord ++ tailWord_4117823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4117823).length < 2 ^ (prefixWord ++ tailWord_4117823).sum := by decide
  have hdescent : baseEnd_4117823 < baseStart_4117823 := by decide
  rcases family_descends (prefixWord ++ tailWord_4117823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4117859 : List Nat := [1, 1, 1, 5, 2, 2, 3, 1, 7]
def baseStart_4117859 : Nat := 118140960795 + 4117859 * 2 ^ 59
def prefixEnd_4117859 : Nat := 4983230072969 + 3 ^ 40 * 4117859 * 2
def baseEnd_4117859 : Nat := 234937881604745510158313

theorem tailTrace_4117859 : CollatzResearch.WordTrace tailWord_4117859 prefixEnd_4117859 234937881604745510158313 := by
  unfold tailWord_4117859
  simp only [CollatzResearch.WordTrace]
  refine ⟨150190656388707592171780631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100127104259138394781187087 150190656388707592171780631)
  ·
    refine ⟨225285984583061388257670947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150190656388707592171780631 225285984583061388257670947)
    ·
      refine ⟨337928976874592082386506421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225285984583061388257670947 337928976874592082386506421)
      ·
        refine ⟨31680841581993007723734977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 337928976874592082386506421 31680841581993007723734977)
        ·
          refine ⟨23760631186494755792801233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31680841581993007723734977 23760631186494755792801233)
          ·
            refine ⟨17820473389871066844600925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23760631186494755792801233 17820473389871066844600925)
            ·
              refine ⟨6682677521201650066725347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17820473389871066844600925 6682677521201650066725347)
              ·
                refine ⟨10024016281802475100088021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6682677521201650066725347 10024016281802475100088021)
                ·
                  refine ⟨234937881604745510158313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10024016281802475100088021 234937881604745510158313)
                  ·
                    rfl

theorem cell23_4117859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 3, 1, 7].length) (baseStart_4117859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4117859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4117859 prefixEnd_4117859 := by exact prefixLift 4117859
  have htrace : WordTrace (prefixWord ++ tailWord_4117859) baseStart_4117859 baseEnd_4117859 := by
    simpa [prefixWord, tailWord_4117859, baseEnd_4117859] using wordTrace_append hprefix tailTrace_4117859
  have hstable : (prefixWord ++ tailWord_4117859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4117859).length < 2 ^ (prefixWord ++ tailWord_4117859).sum := by decide
  have hdescent : baseEnd_4117859 < baseStart_4117859 := by decide
  rcases family_descends (prefixWord ++ tailWord_4117859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4117949 : List Nat := [1, 4, 1, 2, 2, 1, 2, 2, 8]
def baseStart_4117949 : Nat := 118140960795 + 4117949 * 2 ^ 59
def prefixEnd_4117949 : Nat := 4983230072969 + 3 ^ 40 * 4117949 * 2
def baseEnd_4117949 : Nat := 234943016411290471033267

theorem tailTrace_4117949 : CollatzResearch.WordTrace tailWord_4117949 prefixEnd_4117949 234943016411290471033267 := by
  unfold tailWord_4117949
  simp only [CollatzResearch.WordTrace]
  refine ⟨150193938958381537542556901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100129292638921025028371267 150193938958381537542556901)
  ·
    refine ⟨28161363554696538289229419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 150193938958381537542556901 28161363554696538289229419)
    ·
      refine ⟨42242045332044807433844129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28161363554696538289229419 42242045332044807433844129)
      ·
        refine ⟨31681533999033605575383097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42242045332044807433844129 31681533999033605575383097)
        ·
          refine ⟨23761150499275204181537323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31681533999033605575383097 23761150499275204181537323)
          ·
            refine ⟨35641725748912806272305985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23761150499275204181537323 35641725748912806272305985)
            ·
              refine ⟨26731294311684604704229489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35641725748912806272305985 26731294311684604704229489)
              ·
                refine ⟨20048470733763453528172117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26731294311684604704229489 20048470733763453528172117)
                ·
                  refine ⟨234943016411290471033267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 20048470733763453528172117 234943016411290471033267)
                  ·
                    rfl

theorem cell23_4117949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 2, 2, 8].length) (baseStart_4117949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4117949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4117949 prefixEnd_4117949 := by exact prefixLift 4117949
  have htrace : WordTrace (prefixWord ++ tailWord_4117949) baseStart_4117949 baseEnd_4117949 := by
    simpa [prefixWord, tailWord_4117949, baseEnd_4117949] using wordTrace_append hprefix tailTrace_4117949
  have hstable : (prefixWord ++ tailWord_4117949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4117949).length < 2 ^ (prefixWord ++ tailWord_4117949).sum := by decide
  have hdescent : baseEnd_4117949 < baseStart_4117949 := by decide
  rcases family_descends (prefixWord ++ tailWord_4117949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4117956 : List Nat := [2, 3, 3, 2, 1, 1, 1, 1, 2, 1, 6]
def baseStart_4117956 : Nat := 118140960795 + 4117956 * 2 ^ 59
def prefixEnd_4117956 : Nat := 4983230072969 + 3 ^ 40 * 4117956 * 2
def baseEnd_4117956 : Nat := 2114490742066195711911871

theorem tailTrace_4117956 : CollatzResearch.WordTrace tailWord_4117956 prefixEnd_4117956 2114490742066195711911871 := by
  unfold tailWord_4117956
  simp only [CollatzResearch.WordTrace]
  refine ⟨75097097134678088869030861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100129462846237451825374481 75097097134678088869030861)
  ·
    refine ⟨28161411425504283325886573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75097097134678088869030861 28161411425504283325886573)
    ·
      refine ⟨10560529284564106247207465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28161411425504283325886573 10560529284564106247207465)
      ·
        refine ⟨7920396963423079685405599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10560529284564106247207465 7920396963423079685405599)
        ·
          refine ⟨11880595445134619528108399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7920396963423079685405599 11880595445134619528108399)
          ·
            refine ⟨17820893167701929292162599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11880595445134619528108399 17820893167701929292162599)
            ·
              refine ⟨26731339751552893938243899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17820893167701929292162599 26731339751552893938243899)
              ·
                refine ⟨40097009627329340907365849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26731339751552893938243899 40097009627329340907365849)
                ·
                  refine ⟨30072757220497005680524387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40097009627329340907365849 30072757220497005680524387)
                  ·
                    refine ⟨45109135830745508520786581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30072757220497005680524387 45109135830745508520786581)
                    ·
                      refine ⟨2114490742066195711911871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 45109135830745508520786581 2114490742066195711911871)
                      ·
                        rfl

theorem cell23_4117956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 1, 1, 2, 1, 6].length) (baseStart_4117956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4117956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4117956 prefixEnd_4117956 := by exact prefixLift 4117956
  have htrace : WordTrace (prefixWord ++ tailWord_4117956) baseStart_4117956 baseEnd_4117956 := by
    simpa [prefixWord, tailWord_4117956, baseEnd_4117956] using wordTrace_append hprefix tailTrace_4117956
  have hstable : (prefixWord ++ tailWord_4117956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4117956).length < 2 ^ (prefixWord ++ tailWord_4117956).sum := by decide
  have hdescent : baseEnd_4117956 < baseStart_4117956 := by decide
  rcases family_descends (prefixWord ++ tailWord_4117956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4117966 : List Nat := [4, 1, 1, 1, 2, 1, 5, 2, 6]
def baseStart_4117966 : Nat := 118140960795 + 4117966 * 2 ^ 59
def prefixEnd_4117966 : Nat := 4983230072969 + 3 ^ 40 * 4117966 * 2
def baseEnd_4117966 : Nat := 234943986319193408087425

theorem tailTrace_4117966 : CollatzResearch.WordTrace tailWord_4117966 prefixEnd_4117966 234943986319193408087425 := by
  unfold tailWord_4117966
  simp only [CollatzResearch.WordTrace]
  refine ⟨18774319874914993680740719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 100129705999546632963950501 18774319874914993680740719)
  ·
    refine ⟨28161479812372490521111079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18774319874914993680740719 28161479812372490521111079)
    ·
      refine ⟨42242219718558735781666619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28161479812372490521111079 42242219718558735781666619)
      ·
        refine ⟨63363329577838103672499929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42242219718558735781666619 63363329577838103672499929)
        ·
          refine ⟨47522497183378577754374947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63363329577838103672499929 47522497183378577754374947)
          ·
            refine ⟨71283745775067866631562421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47522497183378577754374947 71283745775067866631562421)
            ·
              refine ⟨6682851166412612496708977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 71283745775067866631562421 6682851166412612496708977)
              ·
                refine ⟨5012138374809459372531733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6682851166412612496708977 5012138374809459372531733)
                ·
                  refine ⟨234943986319193408087425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5012138374809459372531733 234943986319193408087425)
                  ·
                    rfl

theorem cell23_4117966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 5, 2, 6].length) (baseStart_4117966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4117966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4117966 prefixEnd_4117966 := by exact prefixLift 4117966
  have htrace : WordTrace (prefixWord ++ tailWord_4117966) baseStart_4117966 baseEnd_4117966 := by
    simpa [prefixWord, tailWord_4117966, baseEnd_4117966] using wordTrace_append hprefix tailTrace_4117966
  have hstable : (prefixWord ++ tailWord_4117966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4117966).length < 2 ^ (prefixWord ++ tailWord_4117966).sum := by decide
  have hdescent : baseEnd_4117966 < baseStart_4117966 := by decide
  rcases family_descends (prefixWord ++ tailWord_4117966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4118009 : List Nat := [1, 2, 1, 3, 1, 2, 1, 3, 3, 6]
def baseStart_4118009 : Nat := 118140960795 + 4118009 * 2 ^ 59
def prefixEnd_4118009 : Nat := 4983230072969 + 3 ^ 40 * 4118009 * 2
def baseEnd_4118009 : Nat := 704839318846961334849709

theorem tailTrace_4118009 : CollatzResearch.WordTrace tailWord_4118009 prefixEnd_4118009 704839318846961334849709 := by
  unfold tailWord_4118009
  simp only [CollatzResearch.WordTrace]
  refine ⟨150196127338164167789741081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100130751558776111859827387 150196127338164167789741081)
  ·
    refine ⟨112647095503623125842305811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150196127338164167789741081 112647095503623125842305811)
    ·
      refine ⟨168970643255434688763458717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112647095503623125842305811 168970643255434688763458717)
      ·
        refine ⟨63363991220788008286297019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 168970643255434688763458717 63363991220788008286297019)
        ·
          refine ⟨95045986831182012429445529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63363991220788008286297019 95045986831182012429445529)
          ·
            refine ⟨71284490123386509322084147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95045986831182012429445529 71284490123386509322084147)
            ·
              refine ⟨106926735185079763983126221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71284490123386509322084147 106926735185079763983126221)
              ·
                refine ⟨40097525694404911493672333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 106926735185079763983126221 40097525694404911493672333)
                ·
                  refine ⟨15036572135401841810127125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40097525694404911493672333 15036572135401841810127125)
                  ·
                    refine ⟨704839318846961334849709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15036572135401841810127125 704839318846961334849709)
                    ·
                      rfl

theorem cell23_4118009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 3, 3, 6].length) (baseStart_4118009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4118009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4118009 prefixEnd_4118009 := by exact prefixLift 4118009
  have htrace : WordTrace (prefixWord ++ tailWord_4118009) baseStart_4118009 baseEnd_4118009 := by
    simpa [prefixWord, tailWord_4118009, baseEnd_4118009] using wordTrace_append hprefix tailTrace_4118009
  have hstable : (prefixWord ++ tailWord_4118009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4118009).length < 2 ^ (prefixWord ++ tailWord_4118009).sum := by decide
  have hdescent : baseEnd_4118009 < baseStart_4118009 := by decide
  rcases family_descends (prefixWord ++ tailWord_4118009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4118027 : List Nat := [1, 1, 1, 1, 9, 1, 1, 1, 3, 1, 3]
def baseStart_4118027 : Nat := 118140960795 + 4118027 * 2 ^ 59
def prefixEnd_4118027 : Nat := 4983230072969 + 3 ^ 40 * 4118027 * 2
def baseEnd_4118027 : Nat := 2114527199192664934124045

theorem tailTrace_4118027 : CollatzResearch.WordTrace tailWord_4118027 prefixEnd_4118027 2114527199192664934124045 := by
  unfold tailWord_4118027
  simp only [CollatzResearch.WordTrace]
  refine ⟨150196783852098956863896335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100131189234732637909264223 150196783852098956863896335)
  ·
    refine ⟨225295175778148435295844503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150196783852098956863896335 225295175778148435295844503)
    ·
      refine ⟨337942763667222652943766755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225295175778148435295844503 337942763667222652943766755)
      ·
        refine ⟨506914145500833979415650133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 337942763667222652943766755 506914145500833979415650133)
        ·
          refine ⟨2970200071293949098138575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 506914145500833979415650133 2970200071293949098138575)
          ·
            refine ⟨4455300106940923647207863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2970200071293949098138575 4455300106940923647207863)
            ·
              refine ⟨6682950160411385470811795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4455300106940923647207863 6682950160411385470811795)
              ·
                refine ⟨10024425240617078206217693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6682950160411385470811795 10024425240617078206217693)
                ·
                  refine ⟨3759159465231404327331635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10024425240617078206217693 3759159465231404327331635)
                  ·
                    refine ⟨5638739197847106490997453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3759159465231404327331635 5638739197847106490997453)
                    ·
                      refine ⟨2114527199192664934124045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5638739197847106490997453 2114527199192664934124045)
                      ·
                        rfl

theorem cell23_4118027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 9, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 9, 1, 1, 1, 3, 1, 3].length) (baseStart_4118027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4118027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4118027 prefixEnd_4118027 := by exact prefixLift 4118027
  have htrace : WordTrace (prefixWord ++ tailWord_4118027) baseStart_4118027 baseEnd_4118027 := by
    simpa [prefixWord, tailWord_4118027, baseEnd_4118027] using wordTrace_append hprefix tailTrace_4118027
  have hstable : (prefixWord ++ tailWord_4118027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4118027).length < 2 ^ (prefixWord ++ tailWord_4118027).sum := by decide
  have hdescent : baseEnd_4118027 < baseStart_4118027 := by decide
  rcases family_descends (prefixWord ++ tailWord_4118027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4118050 : List Nat := [3, 3, 1, 1, 1, 1, 2, 4, 3, 2, 2]
def baseStart_4118050 : Nat := 118140960795 + 4118050 * 2 ^ 59
def prefixEnd_4118050 : Nat := 4983230072969 + 3 ^ 40 * 4118050 * 2
def baseEnd_4118050 : Nat := 2114539009247718344136439

theorem tailTrace_4118050 : CollatzResearch.WordTrace tailWord_4118050 prefixEnd_4118050 2114539009247718344136439 := by
  unfold tailWord_4118050
  simp only [CollatzResearch.WordTrace]
  refine ⟨37549405682753907947995901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100131748487343754527989069 37549405682753907947995901)
  ·
    refine ⟨14081027131032715480498463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37549405682753907947995901 14081027131032715480498463)
    ·
      refine ⟨21121540696549073220747695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14081027131032715480498463 21121540696549073220747695)
      ·
        refine ⟨31682311044823609831121543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21121540696549073220747695 31682311044823609831121543)
        ·
          refine ⟨47523466567235414746682315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31682311044823609831121543 47523466567235414746682315)
          ·
            refine ⟨71285199850853122120023473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47523466567235414746682315 71285199850853122120023473)
            ·
              refine ⟨53463899888139841590017605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71285199850853122120023473 53463899888139841590017605)
              ·
                refine ⟨10024481229026220298128301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53463899888139841590017605 10024481229026220298128301)
                ·
                  refine ⟨3759180460884832611798113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10024481229026220298128301 3759180460884832611798113)
                  ·
                    refine ⟨2819385345663624458848585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3759180460884832611798113 2819385345663624458848585)
                    ·
                      refine ⟨2114539009247718344136439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2819385345663624458848585 2114539009247718344136439)
                      ·
                        rfl

theorem cell23_4118050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 4, 3, 2, 2].length) (baseStart_4118050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4118050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4118050 prefixEnd_4118050 := by exact prefixLift 4118050
  have htrace : WordTrace (prefixWord ++ tailWord_4118050) baseStart_4118050 baseEnd_4118050 := by
    simpa [prefixWord, tailWord_4118050, baseEnd_4118050] using wordTrace_append hprefix tailTrace_4118050
  have hstable : (prefixWord ++ tailWord_4118050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4118050).length < 2 ^ (prefixWord ++ tailWord_4118050).sum := by decide
  have hdescent : baseEnd_4118050 < baseStart_4118050 := by decide
  rcases family_descends (prefixWord ++ tailWord_4118050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4118100 : List Nat := [2, 4, 1, 1, 1, 2, 1, 5, 2, 1, 3]
def baseStart_4118100 : Nat := 118140960795 + 4118100 * 2 ^ 59
def prefixEnd_4118100 : Nat := 4983230072969 + 3 ^ 40 * 4118100 * 2
def baseEnd_4118100 : Nat := 2114564683280443148511209

theorem tailTrace_4118100 : CollatzResearch.WordTrace tailWord_4118100 prefixEnd_4118100 2114564683280443148511209 := by
  unfold tailWord_4118100
  simp only [CollatzResearch.WordTrace]
  refine ⟨75099723190417245165651877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100132964253889660220869169 75099723190417245165651877)
  ·
    refine ⟨14081198098203233468559727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 75099723190417245165651877 14081198098203233468559727)
    ·
      refine ⟨21121797147304850202839591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14081198098203233468559727 21121797147304850202839591)
      ·
        refine ⟨31682695720957275304259387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21121797147304850202839591 31682695720957275304259387)
        ·
          refine ⟨47524043581435912956389081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31682695720957275304259387 47524043581435912956389081)
          ·
            refine ⟨35643032686076934717291811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47524043581435912956389081 35643032686076934717291811)
            ·
              refine ⟨53464549029115402075937717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35643032686076934717291811 53464549029115402075937717)
              ·
                refine ⟨5012301471479568944619161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 53464549029115402075937717 5012301471479568944619161)
                ·
                  refine ⟨3759226103609676708464371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5012301471479568944619161 3759226103609676708464371)
                  ·
                    refine ⟨5638839155414515062696557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3759226103609676708464371 5638839155414515062696557)
                    ·
                      refine ⟨2114564683280443148511209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5638839155414515062696557 2114564683280443148511209)
                      ·
                        rfl

theorem cell23_4118100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 5, 2, 1, 3].length) (baseStart_4118100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4118100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4118100 prefixEnd_4118100 := by exact prefixLift 4118100
  have htrace : WordTrace (prefixWord ++ tailWord_4118100) baseStart_4118100 baseEnd_4118100 := by
    simpa [prefixWord, tailWord_4118100, baseEnd_4118100] using wordTrace_append hprefix tailTrace_4118100
  have hstable : (prefixWord ++ tailWord_4118100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4118100).length < 2 ^ (prefixWord ++ tailWord_4118100).sum := by decide
  have hdescent : baseEnd_4118100 < baseStart_4118100 := by decide
  rcases family_descends (prefixWord ++ tailWord_4118100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4118133 : List Nat := [1, 3, 4, 2, 1, 1, 1, 2, 2, 6]
def baseStart_4118133 : Nat := 118140960795 + 4118133 * 2 ^ 59
def prefixEnd_4118133 : Nat := 4983230072969 + 3 ^ 40 * 4118133 * 2
def baseEnd_4118133 : Nat := 704860542714013839799519

theorem tailTrace_4118133 : CollatzResearch.WordTrace tailWord_4118133 prefixEnd_4118133 704860542714013839799519 := by
  unfold tailWord_4118133
  simp only [CollatzResearch.WordTrace]
  refine ⟨150200649989714936967255053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100133766659809957978170035 150200649989714936967255053)
  ·
    refine ⟨56325243746143101362720645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 150200649989714936967255053 56325243746143101362720645)
    ·
      refine ⟨10560983202401831505510121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 56325243746143101362720645 10560983202401831505510121)
      ·
        refine ⟨7920737401801373629132591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10560983202401831505510121 7920737401801373629132591)
        ·
          refine ⟨11881106102702060443698887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7920737401801373629132591 11881106102702060443698887)
          ·
            refine ⟨17821659154053090665548331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11881106102702060443698887 17821659154053090665548331)
            ·
              refine ⟨26732488731079635998322497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17821659154053090665548331 26732488731079635998322497)
              ·
                refine ⟨20049366548309726998741873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26732488731079635998322497 20049366548309726998741873)
                ·
                  refine ⟨15037024911232295249056405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20049366548309726998741873 15037024911232295249056405)
                  ·
                    refine ⟨704860542714013839799519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15037024911232295249056405 704860542714013839799519)
                    ·
                      rfl

theorem cell23_4118133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 1, 2, 2, 6].length) (baseStart_4118133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4118133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4118133 prefixEnd_4118133 := by exact prefixLift 4118133
  have htrace : WordTrace (prefixWord ++ tailWord_4118133) baseStart_4118133 baseEnd_4118133 := by
    simpa [prefixWord, tailWord_4118133, baseEnd_4118133] using wordTrace_append hprefix tailTrace_4118133
  have hstable : (prefixWord ++ tailWord_4118133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4118133).length < 2 ^ (prefixWord ++ tailWord_4118133).sum := by decide
  have hdescent : baseEnd_4118133 < baseStart_4118133 := by decide
  rcases family_descends (prefixWord ++ tailWord_4118133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4118134 : List Nat := [5, 1, 1, 2, 2, 3, 1, 2, 2, 1, 3]
def baseStart_4118134 : Nat := 118140960795 + 4118134 * 2 ^ 59
def prefixEnd_4118134 : Nat := 4983230072969 + 3 ^ 40 * 4118134 * 2
def baseEnd_4118134 : Nat := 2114582141622696015486053

theorem tailTrace_4118134 : CollatzResearch.WordTrace tailWord_4118134 prefixEnd_4118134 2114582141622696015486053 := by
  unfold tailWord_4118134
  simp only [CollatzResearch.WordTrace]
  refine ⟨9387542903919457133627591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 100133790975140876092027637 9387542903919457133627591)
  ·
    refine ⟨14081314355879185700441387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9387542903919457133627591 14081314355879185700441387)
    ·
      refine ⟨21121971533818778550662081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14081314355879185700441387 21121971533818778550662081)
      ·
        refine ⟨15841478650364083912996561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21121971533818778550662081 15841478650364083912996561)
        ·
          refine ⟨11881108987773062934747421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15841478650364083912996561 11881108987773062934747421)
          ·
            refine ⟨4455415870414898600530283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11881108987773062934747421 4455415870414898600530283)
            ·
              refine ⟨6683123805622347900795425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4455415870414898600530283 6683123805622347900795425)
              ·
                refine ⟨5012342854216760925596569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6683123805622347900795425 5012342854216760925596569)
                ·
                  refine ⟨3759257140662570694197427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5012342854216760925596569 3759257140662570694197427)
                  ·
                    refine ⟨5638885710993856041296141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3759257140662570694197427 5638885710993856041296141)
                    ·
                      refine ⟨2114582141622696015486053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5638885710993856041296141 2114582141622696015486053)
                      ·
                        rfl

theorem cell23_4118134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 3, 1, 2, 2, 1, 3].length) (baseStart_4118134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4118134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4118134 prefixEnd_4118134 := by exact prefixLift 4118134
  have htrace : WordTrace (prefixWord ++ tailWord_4118134) baseStart_4118134 baseEnd_4118134 := by
    simpa [prefixWord, tailWord_4118134, baseEnd_4118134] using wordTrace_append hprefix tailTrace_4118134
  have hstable : (prefixWord ++ tailWord_4118134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4118134).length < 2 ^ (prefixWord ++ tailWord_4118134).sum := by decide
  have hdescent : baseEnd_4118134 < baseStart_4118134 := by decide
  rcases family_descends (prefixWord ++ tailWord_4118134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4118180 : List Nat := [2, 3, 1, 2, 2, 2, 3, 3, 5]
def baseStart_4118180 : Nat := 118140960795 + 4118180 * 2 ^ 59
def prefixEnd_4118180 : Nat := 4983230072969 + 3 ^ 40 * 4118180 * 2
def baseEnd_4118180 : Nat := 234956195748089203945649

theorem tailTrace_4118180 : CollatzResearch.WordTrace tailWord_4118180 prefixEnd_4118180 234956195748089203945649 := by
  unfold tailWord_4118180
  simp only [CollatzResearch.WordTrace]
  refine ⟨75101182110272331997107997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100134909480363109329477329 75101182110272331997107997)
  ·
    refine ⟨28162943291352124498915499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75101182110272331997107997 28162943291352124498915499)
    ·
      refine ⟨42244414937028186748373249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28162943291352124498915499 42244414937028186748373249)
      ·
        refine ⟨31683311202771140061279937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42244414937028186748373249 31683311202771140061279937)
        ·
          refine ⟨23762483402078355045959953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31683311202771140061279937 23762483402078355045959953)
          ·
            refine ⟨17821862551558766284469965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23762483402078355045959953 17821862551558766284469965)
            ·
              refine ⟨6683198456834537356676237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17821862551558766284469965 6683198456834537356676237)
              ·
                refine ⟨2506199421312951508753589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6683198456834537356676237 2506199421312951508753589)
                ·
                  refine ⟨234956195748089203945649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2506199421312951508753589 234956195748089203945649)
                  ·
                    rfl

theorem cell23_4118180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 3, 3, 5].length) (baseStart_4118180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4118180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4118180 prefixEnd_4118180 := by exact prefixLift 4118180
  have htrace : WordTrace (prefixWord ++ tailWord_4118180) baseStart_4118180 baseEnd_4118180 := by
    simpa [prefixWord, tailWord_4118180, baseEnd_4118180] using wordTrace_append hprefix tailTrace_4118180
  have hstable : (prefixWord ++ tailWord_4118180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4118180).length < 2 ^ (prefixWord ++ tailWord_4118180).sum := by decide
  have hdescent : baseEnd_4118180 < baseStart_4118180 := by decide
  rcases family_descends (prefixWord ++ tailWord_4118180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4118197 : List Nat := [1, 3, 3, 3, 3, 1, 1, 1, 7]
def baseStart_4118197 : Nat := 118140960795 + 4118197 * 2 ^ 59
def prefixEnd_4118197 : Nat := 4983230072969 + 3 ^ 40 * 4118197 * 2
def baseEnd_4118197 : Nat := 234957165655992140999807

theorem tailTrace_4118197 : CollatzResearch.WordTrace tailWord_4118197 prefixEnd_4118197 234957165655992140999807 := by
  unfold tailWord_4118197
  simp only [CollatzResearch.WordTrace]
  refine ⟨150202984261483075897584845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100135322840988717265056563 150202984261483075897584845)
  ·
    refine ⟨56326119098056153461594317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 150202984261483075897584845 56326119098056153461594317)
    ·
      refine ⟨21122294661771057548097869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56326119098056153461594317 21122294661771057548097869)
      ·
        refine ⟨7920860498164146580536701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21122294661771057548097869 7920860498164146580536701)
        ·
          refine ⟨2970322686811554967701263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7920860498164146580536701 2970322686811554967701263)
          ·
            refine ⟨4455484030217332451551895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2970322686811554967701263 4455484030217332451551895)
            ·
              refine ⟨6683226045325998677327843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4455484030217332451551895 6683226045325998677327843)
              ·
                refine ⟨10024839067988998015991765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6683226045325998677327843 10024839067988998015991765)
                ·
                  refine ⟨234957165655992140999807, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10024839067988998015991765 234957165655992140999807)
                  ·
                    rfl

theorem cell23_4118197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 3, 1, 1, 1, 7].length) (baseStart_4118197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4118197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4118197 prefixEnd_4118197 := by exact prefixLift 4118197
  have htrace : WordTrace (prefixWord ++ tailWord_4118197) baseStart_4118197 baseEnd_4118197 := by
    simpa [prefixWord, tailWord_4118197, baseEnd_4118197] using wordTrace_append hprefix tailTrace_4118197
  have hstable : (prefixWord ++ tailWord_4118197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4118197).length < 2 ^ (prefixWord ++ tailWord_4118197).sum := by decide
  have hdescent : baseEnd_4118197 < baseStart_4118197 := by decide
  rcases family_descends (prefixWord ++ tailWord_4118197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4118223 : List Nat := [1, 1, 2, 1, 1, 3, 1, 6, 3, 4]
def baseStart_4118223 : Nat := 118140960795 + 4118223 * 2 ^ 59
def prefixEnd_4118223 : Nat := 4983230072969 + 3 ^ 40 * 4118223 * 2
def baseEnd_4118223 : Nat := 704875947133648722424381

theorem tailTrace_4118223 : CollatzResearch.WordTrace tailWord_4118223 prefixEnd_4118223 704875947133648722424381 := by
  unfold tailWord_4118223
  simp only [CollatzResearch.WordTrace]
  refine ⟨150203932559388882338031323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100135955039592588225354215 150203932559388882338031323)
  ·
    refine ⟨225305898839083323507046985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150203932559388882338031323 225305898839083323507046985)
    ·
      refine ⟨168979424129312492630285239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 225305898839083323507046985 168979424129312492630285239)
      ·
        refine ⟨253469136193968738945427859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168979424129312492630285239 253469136193968738945427859)
        ·
          refine ⟨380203704290953108418141789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 253469136193968738945427859 380203704290953108418141789)
          ·
            refine ⟨142576389109107415656803171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 380203704290953108418141789 142576389109107415656803171)
            ·
              refine ⟨213864583663661123485204757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 142576389109107415656803171 213864583663661123485204757)
              ·
                refine ⟨10024902359234115163368973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 213864583663661123485204757 10024902359234115163368973)
                ·
                  refine ⟨3759338384712793186263365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10024902359234115163368973 3759338384712793186263365)
                  ·
                    refine ⟨704875947133648722424381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3759338384712793186263365 704875947133648722424381)
                    ·
                      rfl

theorem cell23_4118223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 6, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 6, 3, 4].length) (baseStart_4118223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4118223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4118223 prefixEnd_4118223 := by exact prefixLift 4118223
  have htrace : WordTrace (prefixWord ++ tailWord_4118223) baseStart_4118223 baseEnd_4118223 := by
    simpa [prefixWord, tailWord_4118223, baseEnd_4118223] using wordTrace_append hprefix tailTrace_4118223
  have hstable : (prefixWord ++ tailWord_4118223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4118223).length < 2 ^ (prefixWord ++ tailWord_4118223).sum := by decide
  have hdescent : baseEnd_4118223 < baseStart_4118223 := by decide
  rcases family_descends (prefixWord ++ tailWord_4118223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4118250 : List Nat := [3, 1, 3, 1, 1, 1, 4, 2, 2, 2, 3]
def baseStart_4118250 : Nat := 118140960795 + 4118250 * 2 ^ 59
def prefixEnd_4118250 : Nat := 4983230072969 + 3 ^ 40 * 4118250 * 2
def baseEnd_4118250 : Nat := 2114641705378617561635519

theorem tailTrace_4118250 : CollatzResearch.WordTrace tailWord_4118250 prefixEnd_4118250 2114641705378617561635519 := by
  unfold tailWord_4118250
  simp only [CollatzResearch.WordTrace]
  refine ⟨37551229332572766487316051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100136611553527377299509469 37551229332572766487316051)
  ·
    refine ⟨56326843998859149730974077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37551229332572766487316051 56326843998859149730974077)
    ·
      refine ⟨21122566499572181149115279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56326843998859149730974077 21122566499572181149115279)
      ·
        refine ⟨31683849749358271723672919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21122566499572181149115279 31683849749358271723672919)
        ·
          refine ⟨47525774624037407585509379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31683849749358271723672919 47525774624037407585509379)
          ·
            refine ⟨71288661936056111378264069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47525774624037407585509379 71288661936056111378264069)
            ·
              refine ⟨13366624113010520883424513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 71288661936056111378264069 13366624113010520883424513)
              ·
                refine ⟨10024968084757890662568385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13366624113010520883424513 10024968084757890662568385)
                ·
                  refine ⟨7518726063568417996926289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10024968084757890662568385 7518726063568417996926289)
                  ·
                    refine ⟨5639044547676313497694717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7518726063568417996926289 5639044547676313497694717)
                    ·
                      refine ⟨2114641705378617561635519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5639044547676313497694717 2114641705378617561635519)
                      ·
                        rfl

theorem cell23_4118250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 4, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 4, 2, 2, 2, 3].length) (baseStart_4118250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4118250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4118250 prefixEnd_4118250 := by exact prefixLift 4118250
  have htrace : WordTrace (prefixWord ++ tailWord_4118250) baseStart_4118250 baseEnd_4118250 := by
    simpa [prefixWord, tailWord_4118250, baseEnd_4118250] using wordTrace_append hprefix tailTrace_4118250
  have hstable : (prefixWord ++ tailWord_4118250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4118250).length < 2 ^ (prefixWord ++ tailWord_4118250).sum := by decide
  have hdescent : baseEnd_4118250 < baseStart_4118250 := by decide
  rcases family_descends (prefixWord ++ tailWord_4118250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4118257 : List Nat := [1, 2, 2, 2, 2, 4, 1, 4, 1, 4]
def baseStart_4118257 : Nat := 118140960795 + 4118257 * 2 ^ 59
def prefixEnd_4118257 : Nat := 4983230072969 + 3 ^ 40 * 4118257 * 2
def baseEnd_4118257 : Nat := 704881766581066344749329

theorem tailTrace_4118257 : CollatzResearch.WordTrace tailWord_4118257 prefixEnd_4118257 704881766581066344749329 := by
  unfold tailWord_4118257
  simp only [CollatzResearch.WordTrace]
  refine ⟨150205172641265706144769025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100136781760843804096512683 150205172641265706144769025)
  ·
    refine ⟨112653879480949279608576769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150205172641265706144769025 112653879480949279608576769)
    ·
      refine ⟨84490409610711959706432577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112653879480949279608576769 84490409610711959706432577)
      ·
        refine ⟨63367807208033969779824433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84490409610711959706432577 63367807208033969779824433)
        ·
          refine ⟨47525855406025477334868325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63367807208033969779824433 47525855406025477334868325)
          ·
            refine ⟨8911097888629777000287811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47525855406025477334868325 8911097888629777000287811)
            ·
              refine ⟨13366646832944665500431717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8911097888629777000287811 13366646832944665500431717)
              ·
                refine ⟨2506246281177124781330947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13366646832944665500431717 2506246281177124781330947)
                ·
                  refine ⟨3759369421765687171996421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2506246281177124781330947 3759369421765687171996421)
                  ·
                    refine ⟨704881766581066344749329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3759369421765687171996421 704881766581066344749329)
                    ·
                      rfl

theorem cell23_4118257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 1, 4, 1, 4].length) (baseStart_4118257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4118257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4118257 prefixEnd_4118257 := by exact prefixLift 4118257
  have htrace : WordTrace (prefixWord ++ tailWord_4118257) baseStart_4118257 baseEnd_4118257 := by
    simpa [prefixWord, tailWord_4118257, baseEnd_4118257] using wordTrace_append hprefix tailTrace_4118257
  have hstable : (prefixWord ++ tailWord_4118257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4118257).length < 2 ^ (prefixWord ++ tailWord_4118257).sum := by decide
  have hdescent : baseEnd_4118257 < baseStart_4118257 := by decide
  rcases family_descends (prefixWord ++ tailWord_4118257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4118283 : List Nat := [1, 1, 1, 1, 5, 1, 4, 1, 3, 5]
def baseStart_4118283 : Nat := 118140960795 + 4118283 * 2 ^ 59
def prefixEnd_4118283 : Nat := 4983230072969 + 3 ^ 40 * 4118283 * 2
def baseEnd_4118283 : Nat := 704886216746738644174289

theorem tailTrace_4118283 : CollatzResearch.WordTrace tailWord_4118283 prefixEnd_4118283 704886216746738644174289 := by
  unfold tailWord_4118283
  simp only [CollatzResearch.WordTrace]
  refine ⟨150206120939171512585215503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100137413959447675056810335 150206120939171512585215503)
  ·
    refine ⟨225309181408757268877823255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150206120939171512585215503 225309181408757268877823255)
    ·
      refine ⟨337963772113135903316734883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225309181408757268877823255 337963772113135903316734883)
      ·
        refine ⟨506945658169703854975102325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 337963772113135903316734883 506945658169703854975102325)
        ·
          refine ⟨47526155453409736403915843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 506945658169703854975102325 47526155453409736403915843)
          ·
            refine ⟨71289233180114604605873765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47526155453409736403915843 71289233180114604605873765)
            ·
              refine ⟨13366731221271488363601331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 71289233180114604605873765 13366731221271488363601331)
              ·
                refine ⟨20050096831907232545401997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13366731221271488363601331 20050096831907232545401997)
                ·
                  refine ⟨7518786311965212204525749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20050096831907232545401997 7518786311965212204525749)
                  ·
                    refine ⟨704886216746738644174289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7518786311965212204525749 704886216746738644174289)
                    ·
                      rfl

theorem cell23_4118283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 4, 1, 3, 5].length) (baseStart_4118283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4118283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4118283 prefixEnd_4118283 := by exact prefixLift 4118283
  have htrace : WordTrace (prefixWord ++ tailWord_4118283) baseStart_4118283 baseEnd_4118283 := by
    simpa [prefixWord, tailWord_4118283, baseEnd_4118283] using wordTrace_append hprefix tailTrace_4118283
  have hstable : (prefixWord ++ tailWord_4118283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4118283).length < 2 ^ (prefixWord ++ tailWord_4118283).sum := by decide
  have hdescent : baseEnd_4118283 < baseStart_4118283 := by decide
  rcases family_descends (prefixWord ++ tailWord_4118283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4118300 : List Nat := [2, 2, 3, 1, 1, 2, 3, 3, 1, 5]
def baseStart_4118300 : Nat := 118140960795 + 4118300 * 2 ^ 59
def prefixEnd_4118300 : Nat := 4983230072969 + 3 ^ 40 * 4118300 * 2
def baseEnd_4118300 : Nat := 704889126470447455336763

theorem tailTrace_4118300 : CollatzResearch.WordTrace tailWord_4118300 prefixEnd_4118300 704889126470447455336763 := by
  unfold tailWord_4118300
  simp only [CollatzResearch.WordTrace]
  refine ⟨75103370490054962244292177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100137827320073282992389569 75103370490054962244292177)
  ·
    refine ⟨56327527867541221683219133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75103370490054962244292177 56327527867541221683219133)
    ·
      refine ⟨21122822950327958131207175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56327527867541221683219133 21122822950327958131207175)
      ·
        refine ⟨31684234425491937196810763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21122822950327958131207175 31684234425491937196810763)
        ·
          refine ⟨47526351638237905795216145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31684234425491937196810763 47526351638237905795216145)
          ·
            refine ⟨35644763728678429346412109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47526351638237905795216145 35644763728678429346412109)
            ·
              refine ⟨13366786398254411004904541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35644763728678429346412109 13366786398254411004904541)
              ·
                refine ⟨5012544899345404126839203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13366786398254411004904541 5012544899345404126839203)
                ·
                  refine ⟨7518817349018106190258805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5012544899345404126839203 7518817349018106190258805)
                  ·
                    refine ⟨704889126470447455336763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7518817349018106190258805 704889126470447455336763)
                    ·
                      rfl

theorem cell23_4118300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 3, 3, 1, 5].length) (baseStart_4118300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4118300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4118300 prefixEnd_4118300 := by exact prefixLift 4118300
  have htrace : WordTrace (prefixWord ++ tailWord_4118300) baseStart_4118300 baseEnd_4118300 := by
    simpa [prefixWord, tailWord_4118300, baseEnd_4118300] using wordTrace_append hprefix tailTrace_4118300
  have hstable : (prefixWord ++ tailWord_4118300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4118300).length < 2 ^ (prefixWord ++ tailWord_4118300).sum := by decide
  have hdescent : baseEnd_4118300 < baseStart_4118300 := by decide
  rcases family_descends (prefixWord ++ tailWord_4118300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4118330 : List Nat := [3, 1, 1, 1, 5, 1, 3, 1, 1, 6]
def baseStart_4118330 : Nat := 118140960795 + 4118330 * 2 ^ 59
def prefixEnd_4118330 : Nat := 4983230072969 + 3 ^ 40 * 4118330 * 2
def baseEnd_4118330 : Nat := 704894261276992416211717

theorem tailTrace_4118330 : CollatzResearch.WordTrace tailWord_4118330 prefixEnd_4118330 704894261276992416211717 := by
  unfold tailWord_4118330
  simp only [CollatzResearch.WordTrace]
  refine ⟨37551958792500309903044111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100138556780000826408117629 37551958792500309903044111)
  ·
    refine ⟨56327938188750464854566167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37551958792500309903044111 56327938188750464854566167)
    ·
      refine ⟨84491907283125697281849251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56327938188750464854566167 84491907283125697281849251)
      ·
        refine ⟨126737860924688545922773877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84491907283125697281849251 126737860924688545922773877)
        ·
          refine ⟨11881674461689551180260051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 126737860924688545922773877 11881674461689551180260051)
          ·
            refine ⟨17822511692534326770390077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11881674461689551180260051 17822511692534326770390077)
            ·
              refine ⟨6683441884700372538896279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17822511692534326770390077 6683441884700372538896279)
              ·
                refine ⟨10025162827050558808344419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6683441884700372538896279 10025162827050558808344419)
                ·
                  refine ⟨15037744240575838212516629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10025162827050558808344419 15037744240575838212516629)
                  ·
                    refine ⟨704894261276992416211717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15037744240575838212516629 704894261276992416211717)
                    ·
                      rfl

theorem cell23_4118330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 3, 1, 1, 6].length) (baseStart_4118330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4118330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4118330 prefixEnd_4118330 := by exact prefixLift 4118330
  have htrace : WordTrace (prefixWord ++ tailWord_4118330) baseStart_4118330 baseEnd_4118330 := by
    simpa [prefixWord, tailWord_4118330, baseEnd_4118330] using wordTrace_append hprefix tailTrace_4118330
  have hstable : (prefixWord ++ tailWord_4118330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4118330).length < 2 ^ (prefixWord ++ tailWord_4118330).sum := by decide
  have hdescent : baseEnd_4118330 < baseStart_4118330 := by decide
  rcases family_descends (prefixWord ++ tailWord_4118330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4118348 : List Nat := [2, 2, 1, 3, 5, 1, 1, 3, 1, 1, 3]
def baseStart_4118348 : Nat := 118140960795 + 4118348 * 2 ^ 59
def prefixEnd_4118348 : Nat := 4983230072969 + 3 ^ 40 * 4118348 * 2
def baseEnd_4118348 : Nat := 2114692026482758178210069

theorem tailTrace_4118348 : CollatzResearch.WordTrace tailWord_4118348 prefixEnd_4118348 2114692026482758178210069 := by
  unfold tailWord_4118348
  simp only [CollatzResearch.WordTrace]
  refine ⟨75104245841968014343165849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100138994455957352457554465 75104245841968014343165849)
  ·
    refine ⟨56328184381476010757374387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75104245841968014343165849 56328184381476010757374387)
    ·
      refine ⟨84492276572214016136061581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56328184381476010757374387 84492276572214016136061581)
      ·
        refine ⟨31684603714580256051023093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84492276572214016136061581 31684603714580256051023093)
        ·
          refine ⟨2970431598241899004783415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 31684603714580256051023093 2970431598241899004783415)
          ·
            refine ⟨4455647397362848507175123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2970431598241899004783415 4455647397362848507175123)
            ·
              refine ⟨6683471096044272760762685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4455647397362848507175123 6683471096044272760762685)
              ·
                refine ⟨2506301661016602285286007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6683471096044272760762685 2506301661016602285286007)
                ·
                  refine ⟨3759452491524903427929011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2506301661016602285286007 3759452491524903427929011)
                  ·
                    refine ⟨5639178737287355141893517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3759452491524903427929011 5639178737287355141893517)
                    ·
                      refine ⟨2114692026482758178210069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5639178737287355141893517 2114692026482758178210069)
                      ·
                        rfl

theorem cell23_4118348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 5, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 5, 1, 1, 3, 1, 1, 3].length) (baseStart_4118348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4118348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4118348 prefixEnd_4118348 := by exact prefixLift 4118348
  have htrace : WordTrace (prefixWord ++ tailWord_4118348) baseStart_4118348 baseEnd_4118348 := by
    simpa [prefixWord, tailWord_4118348, baseEnd_4118348] using wordTrace_append hprefix tailTrace_4118348
  have hstable : (prefixWord ++ tailWord_4118348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4118348).length < 2 ^ (prefixWord ++ tailWord_4118348).sum := by decide
  have hdescent : baseEnd_4118348 < baseStart_4118348 := by decide
  rcases family_descends (prefixWord ++ tailWord_4118348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4118357 : List Nat := [1, 3, 2, 2, 2, 2, 2, 3, 1, 2, 3]
def baseStart_4118357 : Nat := 118140960795 + 4118357 * 2 ^ 59
def prefixEnd_4118357 : Nat := 4983230072969 + 3 ^ 40 * 4118357 * 2
def baseEnd_4118357 : Nat := 2114696647808648642997527

theorem tailTrace_4118357 : CollatzResearch.WordTrace tailWord_4118357 prefixEnd_4118357 2114696647808648642997527 := by
  unfold tailWord_4118357
  simp only [CollatzResearch.WordTrace]
  refine ⟨150208819940903423223409325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100139213293935615482272883 150208819940903423223409325)
  ·
    refine ⟨56328307477838783708778497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 150208819940903423223409325 56328307477838783708778497)
    ·
      refine ⟨42246230608379087781583873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56328307477838783708778497 42246230608379087781583873)
      ·
        refine ⟨31684672956284315836187905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42246230608379087781583873 31684672956284315836187905)
        ·
          refine ⟨23763504717213236877140929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31684672956284315836187905 23763504717213236877140929)
          ·
            refine ⟨17822628537909927657855697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23763504717213236877140929 17822628537909927657855697)
            ·
              refine ⟨13366971403432445743391773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17822628537909927657855697 13366971403432445743391773)
              ·
                refine ⟨5012614276287167153771915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13366971403432445743391773 5012614276287167153771915)
                ·
                  refine ⟨7518921414430750730657873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5012614276287167153771915 7518921414430750730657873)
                  ·
                    refine ⟨5639191060823063047993405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7518921414430750730657873 5639191060823063047993405)
                    ·
                      refine ⟨2114696647808648642997527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5639191060823063047993405 2114696647808648642997527)
                      ·
                        rfl

theorem cell23_4118357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 2, 3, 1, 2, 3].length) (baseStart_4118357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4118357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4118357 prefixEnd_4118357 := by exact prefixLift 4118357
  have htrace : WordTrace (prefixWord ++ tailWord_4118357) baseStart_4118357 baseEnd_4118357 := by
    simpa [prefixWord, tailWord_4118357, baseEnd_4118357] using wordTrace_append hprefix tailTrace_4118357
  have hstable : (prefixWord ++ tailWord_4118357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4118357).length < 2 ^ (prefixWord ++ tailWord_4118357).sum := by decide
  have hdescent : baseEnd_4118357 < baseStart_4118357 := by decide
  rcases family_descends (prefixWord ++ tailWord_4118357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4118371 : List Nat := [1, 1, 1, 5, 4, 2, 1, 1, 3, 2, 2]
def baseStart_4118371 : Nat := 118140960795 + 4118371 * 2 ^ 59
def prefixEnd_4118371 : Nat := 4983230072969 + 3 ^ 40 * 4118371 * 2
def baseEnd_4118371 : Nat := 2114703836537811588222463

theorem tailTrace_4118371 : CollatzResearch.WordTrace tailWord_4118371 prefixEnd_4118371 2114703836537811588222463 := by
  unfold tailWord_4118371
  simp only [CollatzResearch.WordTrace]
  refine ⟨150209330562852703614418967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100139553708568469076279311 150209330562852703614418967)
  ·
    refine ⟨225313995844279055421628451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150209330562852703614418967 225313995844279055421628451)
    ·
      refine ⟨337970993766418583132442677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225313995844279055421628451 337970993766418583132442677)
      ·
        refine ⟨31684780665601742168666501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 337970993766418583132442677 31684780665601742168666501)
        ·
          refine ⟨5940896374800326656624969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31684780665601742168666501 5940896374800326656624969)
          ·
            refine ⟨4455672281100244992468727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5940896374800326656624969 4455672281100244992468727)
            ·
              refine ⟨6683508421650367488703091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4455672281100244992468727 6683508421650367488703091)
              ·
                refine ⟨10025262632475551233054637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6683508421650367488703091 10025262632475551233054637)
                ·
                  refine ⟨3759473487178331712395489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10025262632475551233054637 3759473487178331712395489)
                  ·
                    refine ⟨2819605115383748784296617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3759473487178331712395489 2819605115383748784296617)
                    ·
                      refine ⟨2114703836537811588222463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2819605115383748784296617 2114703836537811588222463)
                      ·
                        rfl

theorem cell23_4118371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 2, 1, 1, 3, 2, 2].length) (baseStart_4118371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4118371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4118371 prefixEnd_4118371 := by exact prefixLift 4118371
  have htrace : WordTrace (prefixWord ++ tailWord_4118371) baseStart_4118371 baseEnd_4118371 := by
    simpa [prefixWord, tailWord_4118371, baseEnd_4118371] using wordTrace_append hprefix tailTrace_4118371
  have hstable : (prefixWord ++ tailWord_4118371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4118371).length < 2 ^ (prefixWord ++ tailWord_4118371).sum := by decide
  have hdescent : baseEnd_4118371 < baseStart_4118371 := by decide
  rcases family_descends (prefixWord ++ tailWord_4118371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4118373 : List Nat := [1, 3, 1, 3, 1, 1, 1, 3, 2, 7]
def baseStart_4118373 : Nat := 118140960795 + 4118373 * 2 ^ 59
def prefixEnd_4118373 : Nat := 4983230072969 + 3 ^ 40 * 4118373 * 2
def baseEnd_4118373 : Nat := 704901621166373526799151

theorem tailTrace_4118373 : CollatzResearch.WordTrace tailWord_4118373 prefixEnd_4118373 704901621166373526799151 := by
  unfold tailWord_4118373
  simp only [CollatzResearch.WordTrace]
  refine ⟨150209403508845457955991773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100139602339230305303994515 150209403508845457955991773)
  ·
    refine ⟨56328526315817046733496915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 150209403508845457955991773 56328526315817046733496915)
    ·
      refine ⟨84492789473725570100245373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56328526315817046733496915 84492789473725570100245373)
      ·
        refine ⟨31684796052647088787592015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84492789473725570100245373 31684796052647088787592015)
        ·
          refine ⟨47527194078970633181388023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31684796052647088787592015 47527194078970633181388023)
          ·
            refine ⟨71290791118455949772082035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47527194078970633181388023 71290791118455949772082035)
            ·
              refine ⟨106936186677683924658123053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71290791118455949772082035 106936186677683924658123053)
              ·
                refine ⟨40101070004131471746796145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 106936186677683924658123053 40101070004131471746796145)
                ·
                  refine ⟨30075802503098603810097109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40101070004131471746796145 30075802503098603810097109)
                  ·
                    refine ⟨704901621166373526799151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 30075802503098603810097109 704901621166373526799151)
                    ·
                      rfl

theorem cell23_4118373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 3, 2, 7].length) (baseStart_4118373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4118373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4118373 prefixEnd_4118373 := by exact prefixLift 4118373
  have htrace : WordTrace (prefixWord ++ tailWord_4118373) baseStart_4118373 baseEnd_4118373 := by
    simpa [prefixWord, tailWord_4118373, baseEnd_4118373] using wordTrace_append hprefix tailTrace_4118373
  have hstable : (prefixWord ++ tailWord_4118373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4118373).length < 2 ^ (prefixWord ++ tailWord_4118373).sum := by decide
  have hdescent : baseEnd_4118373 < baseStart_4118373 := by decide
  rcases family_descends (prefixWord ++ tailWord_4118373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4118422 : List Nat := [5, 3, 1, 1, 2, 1, 1, 4, 1, 2, 2]
def baseStart_4118422 : Nat := 118140960795 + 4118422 * 2 ^ 59
def prefixEnd_4118422 : Nat := 4983230072969 + 3 ^ 40 * 4118422 * 2
def baseEnd_4118422 : Nat := 2114730024051190888684729

theorem tailTrace_4118422 : CollatzResearch.WordTrace tailWord_4118422 prefixEnd_4118422 2114730024051190888684729 := by
  unfold tailWord_4118422
  simp only [CollatzResearch.WordTrace]
  refine ⟨9388199417854246207782845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 100140793790445292883017013 9388199417854246207782845)
  ·
    refine ⟨3520574781695342327918567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9388199417854246207782845 3520574781695342327918567)
    ·
      refine ⟨5280862172543013491877851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3520574781695342327918567 5280862172543013491877851)
      ·
        refine ⟨7921293258814520237816777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5280862172543013491877851 7921293258814520237816777)
        ·
          refine ⟨5940969944110890178362583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7921293258814520237816777 5940969944110890178362583)
          ·
            refine ⟨8911454916166335267543875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5940969944110890178362583 8911454916166335267543875)
            ·
              refine ⟨13367182374249502901315813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8911454916166335267543875 13367182374249502901315813)
              ·
                refine ⟨2506346695171781793996715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13367182374249502901315813 2506346695171781793996715)
                ·
                  refine ⟨3759520042757672690995073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2506346695171781793996715 3759520042757672690995073)
                  ·
                    refine ⟨2819640032068254518246305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3759520042757672690995073 2819640032068254518246305)
                    ·
                      refine ⟨2114730024051190888684729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2819640032068254518246305 2114730024051190888684729)
                      ·
                        rfl

theorem cell23_4118422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 1, 4, 1, 2, 2].length) (baseStart_4118422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4118422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4118422 prefixEnd_4118422 := by exact prefixLift 4118422
  have htrace : WordTrace (prefixWord ++ tailWord_4118422) baseStart_4118422 baseEnd_4118422 := by
    simpa [prefixWord, tailWord_4118422, baseEnd_4118422] using wordTrace_append hprefix tailTrace_4118422
  have hstable : (prefixWord ++ tailWord_4118422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4118422).length < 2 ^ (prefixWord ++ tailWord_4118422).sum := by decide
  have hdescent : baseEnd_4118422 < baseStart_4118422 := by decide
  rcases family_descends (prefixWord ++ tailWord_4118422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4118480 : List Nat := [2, 1, 1, 1, 1, 2, 4, 4, 2, 5]
def baseStart_4118480 : Nat := 118140960795 + 4118480 * 2 ^ 59
def prefixEnd_4118480 : Nat := 4983230072969 + 3 ^ 40 * 4118480 * 2
def baseEnd_4118480 : Nat := 704919935309717220586487

theorem tailTrace_4118480 : CollatzResearch.WordTrace tailWord_4118480 prefixEnd_4118480 704919935309717220586487 := by
  unfold tailWord_4118480
  simp only [CollatzResearch.WordTrace]
  refine ⟨75106653059728907615068447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100142204079638543486757929 75106653059728907615068447)
  ·
    refine ⟨112659979589593361422602671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75106653059728907615068447 112659979589593361422602671)
    ·
      refine ⟨168989969384390042133904007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112659979589593361422602671 168989969384390042133904007)
      ·
        refine ⟨253484954076585063200856011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168989969384390042133904007 253484954076585063200856011)
        ·
          refine ⟨380227431114877594801284017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 253484954076585063200856011 380227431114877594801284017)
          ·
            refine ⟨285170573336158196100963013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 380227431114877594801284017 285170573336158196100963013)
            ·
              refine ⟨53469482500529661768930565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 285170573336158196100963013 53469482500529661768930565)
              ·
                refine ⟨10025527968849311581674481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53469482500529661768930565 10025527968849311581674481)
                ·
                  refine ⟨7519145976636983686255861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10025527968849311581674481 7519145976636983686255861)
                  ·
                    refine ⟨704919935309717220586487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7519145976636983686255861 704919935309717220586487)
                    ·
                      rfl

theorem cell23_4118480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 4, 2, 5].length) (baseStart_4118480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4118480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4118480 prefixEnd_4118480 := by exact prefixLift 4118480
  have htrace : WordTrace (prefixWord ++ tailWord_4118480) baseStart_4118480 baseEnd_4118480 := by
    simpa [prefixWord, tailWord_4118480, baseEnd_4118480] using wordTrace_append hprefix tailTrace_4118480
  have hstable : (prefixWord ++ tailWord_4118480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4118480).length < 2 ^ (prefixWord ++ tailWord_4118480).sum := by decide
  have hdescent : baseEnd_4118480 < baseStart_4118480 := by decide
  rcases family_descends (prefixWord ++ tailWord_4118480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4118500 : List Nat := [2, 3, 1, 1, 1, 1, 3, 1, 3, 3, 4]
def baseStart_4118500 : Nat := 118140960795 + 4118500 * 2 ^ 59
def prefixEnd_4118500 : Nat := 4983230072969 + 3 ^ 40 * 4118500 * 2
def baseEnd_4118500 : Nat := 2114770075542241583509369

theorem tailTrace_4118500 : CollatzResearch.WordTrace tailWord_4118500 prefixEnd_4118500 2114770075542241583509369 := by
  unfold tailWord_4118500
  simp only [CollatzResearch.WordTrace]
  refine ⟨75107017789692679322932477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100142690386256905763909969 75107017789692679322932477)
  ·
    refine ⟨28165131671134754746099679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75107017789692679322932477 28165131671134754746099679)
    ·
      refine ⟨42247697506702132119149519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28165131671134754746099679 42247697506702132119149519)
      ·
        refine ⟨63371546260053198178724279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42247697506702132119149519 63371546260053198178724279)
        ·
          refine ⟨95057319390079797268086419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63371546260053198178724279 95057319390079797268086419)
          ·
            refine ⟨142585979085119695902129629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95057319390079797268086419 142585979085119695902129629)
            ·
              refine ⟨53469742156919885963298611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 142585979085119695902129629 53469742156919885963298611)
              ·
                refine ⟨80204613235379828944947917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53469742156919885963298611 80204613235379828944947917)
                ·
                  refine ⟨30076729963267435854355469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 80204613235379828944947917 30076729963267435854355469)
                  ·
                    refine ⟨11278773736225288445383301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30076729963267435854355469 11278773736225288445383301)
                    ·
                      refine ⟨2114770075542241583509369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11278773736225288445383301 2114770075542241583509369)
                      ·
                        rfl

theorem cell23_4118500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 1, 3, 3, 4].length) (baseStart_4118500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4118500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4118500 prefixEnd_4118500 := by exact prefixLift 4118500
  have htrace : WordTrace (prefixWord ++ tailWord_4118500) baseStart_4118500 baseEnd_4118500 := by
    simpa [prefixWord, tailWord_4118500, baseEnd_4118500] using wordTrace_append hprefix tailTrace_4118500
  have hstable : (prefixWord ++ tailWord_4118500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4118500).length < 2 ^ (prefixWord ++ tailWord_4118500).sum := by decide
  have hdescent : baseEnd_4118500 < baseStart_4118500 := by decide
  rcases family_descends (prefixWord ++ tailWord_4118500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4118518 : List Nat := [5, 1, 1, 1, 5, 1, 1, 3, 5]
def baseStart_4118518 : Nat := 118140960795 + 4118518 * 2 ^ 59
def prefixEnd_4118518 : Nat := 4983230072969 + 3 ^ 40 * 4118518 * 2
def baseEnd_4118518 : Nat := 234975479799335834787143

theorem tailTrace_4118518 : CollatzResearch.WordTrace tailWord_4118518 prefixEnd_4118518 234975479799335834787143 := by
  unfold tailWord_4118518
  simp only [CollatzResearch.WordTrace]
  refine ⟨9388418255832509232501263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 100143128062213431813346805 9388418255832509232501263)
  ·
    refine ⟨14082627383748763848751895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9388418255832509232501263 14082627383748763848751895)
    ·
      refine ⟨21123941075623145773127843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14082627383748763848751895 21123941075623145773127843)
      ·
        refine ⟨31685911613434718659691765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21123941075623145773127843 31685911613434718659691765)
        ·
          refine ⟨2970554213759504874346103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 31685911613434718659691765 2970554213759504874346103)
          ·
            refine ⟨4455831320639257311519155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2970554213759504874346103 4455831320639257311519155)
            ·
              refine ⟨6683746980958885967278733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4455831320639257311519155 6683746980958885967278733)
              ·
                refine ⟨2506405117859582237729525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6683746980958885967278733 2506405117859582237729525)
                ·
                  refine ⟨234975479799335834787143, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2506405117859582237729525 234975479799335834787143)
                  ·
                    rfl

theorem cell23_4118518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 5, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 5, 1, 1, 3, 5].length) (baseStart_4118518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4118518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4118518 prefixEnd_4118518 := by exact prefixLift 4118518
  have htrace : WordTrace (prefixWord ++ tailWord_4118518) baseStart_4118518 baseEnd_4118518 := by
    simpa [prefixWord, tailWord_4118518, baseEnd_4118518] using wordTrace_append hprefix tailTrace_4118518
  have hstable : (prefixWord ++ tailWord_4118518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4118518).length < 2 ^ (prefixWord ++ tailWord_4118518).sum := by decide
  have hdescent : baseEnd_4118518 < baseStart_4118518 := by decide
  rcases family_descends (prefixWord ++ tailWord_4118518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4118540 : List Nat := [2, 2, 1, 2, 3, 1, 1, 3, 8]
def baseStart_4118540 : Nat := 118140960795 + 4118540 * 2 ^ 59
def prefixEnd_4118540 : Nat := 4983230072969 + 3 ^ 40 * 4118540 * 2
def baseEnd_4118540 : Nat := 234976734974269047445465

theorem tailTrace_4118540 : CollatzResearch.WordTrace tailWord_4118540 prefixEnd_4118540 234976734974269047445465 := by
  unfold tailWord_4118540
  simp only [CollatzResearch.WordTrace]
  refine ⟨75107747249620222738660537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100143662999493630318214049 75107747249620222738660537)
  ·
    refine ⟨56330810437215167053995403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75107747249620222738660537 56330810437215167053995403)
    ·
      refine ⟨84496215655822750580993105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56330810437215167053995403 84496215655822750580993105)
      ·
        refine ⟨63372161741867062935744829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84496215655822750580993105 63372161741867062935744829)
        ·
          refine ⟨23764560653200148600904311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63372161741867062935744829 23764560653200148600904311)
          ·
            refine ⟨35646840979800222901356467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23764560653200148600904311 35646840979800222901356467)
            ·
              refine ⟨53470261469700334352034701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35646840979800222901356467 53470261469700334352034701)
              ·
                refine ⟨20051348051137625382013013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53470261469700334352034701 20051348051137625382013013)
                ·
                  refine ⟨234976734974269047445465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 20051348051137625382013013 234976734974269047445465)
                  ·
                    rfl

theorem cell23_4118540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 3, 8].length) (baseStart_4118540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4118540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4118540 prefixEnd_4118540 := by exact prefixLift 4118540
  have htrace : WordTrace (prefixWord ++ tailWord_4118540) baseStart_4118540 baseEnd_4118540 := by
    simpa [prefixWord, tailWord_4118540, baseEnd_4118540] using wordTrace_append hprefix tailTrace_4118540
  have hstable : (prefixWord ++ tailWord_4118540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4118540).length < 2 ^ (prefixWord ++ tailWord_4118540).sum := by decide
  have hdescent : baseEnd_4118540 < baseStart_4118540 := by decide
  rcases family_descends (prefixWord ++ tailWord_4118540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4118601 : List Nat := [1, 2, 1, 1, 2, 2, 5, 4, 1, 1, 3]
def baseStart_4118601 : Nat := 118140960795 + 4118601 * 2 ^ 59
def prefixEnd_4118601 : Nat := 4983230072969 + 3 ^ 40 * 4118601 * 2
def baseEnd_4118601 : Nat := 2114821937088345688346405

theorem tailTrace_4118601 : CollatzResearch.WordTrace tailWord_4118601 prefixEnd_4118601 2114821937088345688346405 := by
  unfold tailWord_4118601
  simp only [CollatzResearch.WordTrace]
  refine ⟨150217719352019452895291657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100145146234679635263527771 150217719352019452895291657)
  ·
    refine ⟨112663289514014589671468743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150217719352019452895291657 112663289514014589671468743)
    ·
      refine ⟨168994934271021884507203115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112663289514014589671468743 168994934271021884507203115)
      ·
        refine ⟨253492401406532826760804673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168994934271021884507203115 253492401406532826760804673)
        ·
          refine ⟨190119301054899620070603505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 253492401406532826760804673 190119301054899620070603505)
          ·
            refine ⟨142589475791174715052952629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 190119301054899620070603505 142589475791174715052952629)
            ·
              refine ⟨13367763355422629536214309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 142589475791174715052952629 13367763355422629536214309)
              ·
                refine ⟨2506455629141743038040183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13367763355422629536214309 2506455629141743038040183)
                ·
                  refine ⟨3759683443712614557060275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2506455629141743038040183 3759683443712614557060275)
                  ·
                    refine ⟨5639525165568921835590413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3759683443712614557060275 5639525165568921835590413)
                    ·
                      refine ⟨2114821937088345688346405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5639525165568921835590413 2114821937088345688346405)
                      ·
                        rfl

theorem cell23_4118601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 5, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 5, 4, 1, 1, 3].length) (baseStart_4118601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4118601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4118601 prefixEnd_4118601 := by exact prefixLift 4118601
  have htrace : WordTrace (prefixWord ++ tailWord_4118601) baseStart_4118601 baseEnd_4118601 := by
    simpa [prefixWord, tailWord_4118601, baseEnd_4118601] using wordTrace_append hprefix tailTrace_4118601
  have hstable : (prefixWord ++ tailWord_4118601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4118601).length < 2 ^ (prefixWord ++ tailWord_4118601).sum := by decide
  have hdescent : baseEnd_4118601 < baseStart_4118601 := by decide
  rcases family_descends (prefixWord ++ tailWord_4118601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4118617 : List Nat := [1, 2, 1, 2, 2, 1, 6, 1, 1, 6]
def baseStart_4118617 : Nat := 118140960795 + 4118617 * 2 ^ 59
def prefixEnd_4118617 : Nat := 4983230072969 + 3 ^ 40 * 4118617 * 2
def baseEnd_4118617 : Nat := 704943384259605875248777

theorem tailTrace_4118617 : CollatzResearch.WordTrace tailWord_4118617 prefixEnd_4118617 704943384259605875248777 := by
  unfold tailWord_4118617
  simp only [CollatzResearch.WordTrace]
  refine ⟨150218302919961487627874105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100145535279974325085249403 150218302919961487627874105)
  ·
    refine ⟨112663727189971115720905579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150218302919961487627874105 112663727189971115720905579)
    ·
      refine ⟨168995590784956673581358369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112663727189971115720905579 168995590784956673581358369)
      ·
        refine ⟨126746693088717505186018777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 168995590784956673581358369 126746693088717505186018777)
        ·
          refine ⟨95060019816538128889514083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126746693088717505186018777 95060019816538128889514083)
          ·
            refine ⟨142590029724807193334271125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95060019816538128889514083 142590029724807193334271125)
            ·
              refine ⟨6683907643350337187543959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 142590029724807193334271125 6683907643350337187543959)
              ·
                refine ⟨10025861465025505781315939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6683907643350337187543959 10025861465025505781315939)
                ·
                  refine ⟨15038792197538258671973909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10025861465025505781315939 15038792197538258671973909)
                  ·
                    refine ⟨704943384259605875248777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15038792197538258671973909 704943384259605875248777)
                    ·
                      rfl

theorem cell23_4118617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 6, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 6, 1, 1, 6].length) (baseStart_4118617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4118617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4118617 prefixEnd_4118617 := by exact prefixLift 4118617
  have htrace : WordTrace (prefixWord ++ tailWord_4118617) baseStart_4118617 baseEnd_4118617 := by
    simpa [prefixWord, tailWord_4118617, baseEnd_4118617] using wordTrace_append hprefix tailTrace_4118617
  have hstable : (prefixWord ++ tailWord_4118617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4118617).length < 2 ^ (prefixWord ++ tailWord_4118617).sum := by decide
  have hdescent : baseEnd_4118617 < baseStart_4118617 := by decide
  rcases family_descends (prefixWord ++ tailWord_4118617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4118622 : List Nat := [4, 4, 1, 1, 3, 1, 1, 1, 2, 2, 3]
def baseStart_4118622 : Nat := 118140960795 + 4118622 * 2 ^ 59
def prefixEnd_4118622 : Nat := 4983230072969 + 3 ^ 40 * 4118622 * 2
def baseEnd_4118622 : Nat := 2114832720182090106183809

theorem tailTrace_4118622 : CollatzResearch.WordTrace tailWord_4118622 prefixEnd_4118622 2114832720182090106183809 := by
  unfold tailWord_4118622
  simp only [CollatzResearch.WordTrace]
  refine ⟨18777310660617921685225765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 100145656856628915654537413 18777310660617921685225765)
  ·
    refine ⟨3520745748865860315979831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18777310660617921685225765 3520745748865860315979831)
    ·
      refine ⟨5281118623298790473969747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3520745748865860315979831 5281118623298790473969747)
      ·
        refine ⟨7921677934948185710954621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5281118623298790473969747 7921677934948185710954621)
        ·
          refine ⟨2970629225605569641607983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7921677934948185710954621 2970629225605569641607983)
          ·
            refine ⟨4455943838408354462411975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2970629225605569641607983 4455943838408354462411975)
            ·
              refine ⟨6683915757612531693617963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4455943838408354462411975 6683915757612531693617963)
              ·
                refine ⟨10025873636418797540426945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6683915757612531693617963 10025873636418797540426945)
                ·
                  refine ⟨7519405227314098155320209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10025873636418797540426945 7519405227314098155320209)
                  ·
                    refine ⟨5639553920485573616490157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7519405227314098155320209 5639553920485573616490157)
                    ·
                      refine ⟨2114832720182090106183809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5639553920485573616490157 2114832720182090106183809)
                      ·
                        rfl

theorem cell23_4118622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 3, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 3, 1, 1, 1, 2, 2, 3].length) (baseStart_4118622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4118622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4118622 prefixEnd_4118622 := by exact prefixLift 4118622
  have htrace : WordTrace (prefixWord ++ tailWord_4118622) baseStart_4118622 baseEnd_4118622 := by
    simpa [prefixWord, tailWord_4118622, baseEnd_4118622] using wordTrace_append hprefix tailTrace_4118622
  have hstable : (prefixWord ++ tailWord_4118622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4118622).length < 2 ^ (prefixWord ++ tailWord_4118622).sum := by decide
  have hdescent : baseEnd_4118622 < baseStart_4118622 := by decide
  rcases family_descends (prefixWord ++ tailWord_4118622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4118692 : List Nat := [2, 3, 1, 2, 4, 2, 1, 3, 1, 2, 2]
def baseStart_4118692 : Nat := 118140960795 + 4118692 * 2 ^ 59
def prefixEnd_4118692 : Nat := 4983230072969 + 3 ^ 40 * 4118692 * 2
def baseEnd_4118692 : Nat := 2114868663827904832308487

theorem tailTrace_4118692 : CollatzResearch.WordTrace tailWord_4118692 prefixEnd_4118692 2114868663827904832308487 := by
  unfold tailWord_4118692
  simp only [CollatzResearch.WordTrace]
  refine ⟨75110519197344887718427165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100147358929793183624569553 75110519197344887718427165)
  ·
    refine ⟨28166444699004332894410187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75110519197344887718427165 28166444699004332894410187)
    ·
      refine ⟨42249667048506499341615281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28166444699004332894410187 42249667048506499341615281)
      ·
        refine ⟨31687250286379874506211461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42249667048506499341615281 31687250286379874506211461)
        ·
          refine ⟨5941359428696226469914649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31687250286379874506211461 5941359428696226469914649)
          ·
            refine ⟨4456019571522169852435987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5941359428696226469914649 4456019571522169852435987)
            ·
              refine ⟨6684029357283254778653981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4456019571522169852435987 6684029357283254778653981)
              ·
                refine ⟨2506511008981220541995243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6684029357283254778653981 2506511008981220541995243)
                ·
                  refine ⟨3759766513471830812992865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2506511008981220541995243 3759766513471830812992865)
                  ·
                    refine ⟨2819824885103873109744649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3759766513471830812992865 2819824885103873109744649)
                    ·
                      refine ⟨2114868663827904832308487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2819824885103873109744649 2114868663827904832308487)
                      ·
                        rfl

theorem cell23_4118692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 2, 1, 3, 1, 2, 2].length) (baseStart_4118692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4118692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4118692 prefixEnd_4118692 := by exact prefixLift 4118692
  have htrace : WordTrace (prefixWord ++ tailWord_4118692) baseStart_4118692 baseEnd_4118692 := by
    simpa [prefixWord, tailWord_4118692, baseEnd_4118692] using wordTrace_append hprefix tailTrace_4118692
  have hstable : (prefixWord ++ tailWord_4118692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4118692).length < 2 ^ (prefixWord ++ tailWord_4118692).sum := by decide
  have hdescent : baseEnd_4118692 < baseStart_4118692 := by decide
  rcases family_descends (prefixWord ++ tailWord_4118692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4118709 : List Nat := [1, 3, 3, 4, 1, 1, 3, 2, 1, 2, 2]
def baseStart_4118709 : Nat := 118140960795 + 4118709 * 2 ^ 59
def prefixEnd_4118709 : Nat := 4983230072969 + 3 ^ 40 * 4118709 * 2
def baseEnd_4118709 : Nat := 2114877392999031265795909

theorem tailTrace_4118709 : CollatzResearch.WordTrace tailWord_4118709 prefixEnd_4118709 2114877392999031265795909 := by
  unfold tailWord_4118709
  simp only [CollatzResearch.WordTrace]
  refine ⟨150221658435628187340223181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100147772290418791560148787 150221658435628187340223181)
  ·
    refine ⟨56333121913360570252583693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 150221658435628187340223181 56333121913360570252583693)
    ·
      refine ⟨21124920717510213844718885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56333121913360570252583693 21124920717510213844718885)
      ·
        refine ⟨3960922634533165095884791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21124920717510213844718885 3960922634533165095884791)
        ·
          refine ⟨5941383951799747643827187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3960922634533165095884791 5941383951799747643827187)
          ·
            refine ⟨8912075927699621465740781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5941383951799747643827187 8912075927699621465740781)
            ·
              refine ⟨3342028472887358049652793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8912075927699621465740781 3342028472887358049652793)
              ·
                refine ⟨2506521354665518537239595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3342028472887358049652793 2506521354665518537239595)
                ·
                  refine ⟨3759782031998277805859393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2506521354665518537239595 3759782031998277805859393)
                  ·
                    refine ⟨2819836523998708354394545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3759782031998277805859393 2819836523998708354394545)
                    ·
                      refine ⟨2114877392999031265795909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2819836523998708354394545 2114877392999031265795909)
                      ·
                        rfl

theorem cell23_4118709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 3, 2, 1, 2, 2].length) (baseStart_4118709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4118709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4118709 prefixEnd_4118709 := by exact prefixLift 4118709
  have htrace : WordTrace (prefixWord ++ tailWord_4118709) baseStart_4118709 baseEnd_4118709 := by
    simpa [prefixWord, tailWord_4118709, baseEnd_4118709] using wordTrace_append hprefix tailTrace_4118709
  have hstable : (prefixWord ++ tailWord_4118709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4118709).length < 2 ^ (prefixWord ++ tailWord_4118709).sum := by decide
  have hdescent : baseEnd_4118709 < baseStart_4118709 := by decide
  rcases family_descends (prefixWord ++ tailWord_4118709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4118717 : List Nat := [1, 4, 1, 2, 1, 1, 1, 1, 3, 3, 5]
def baseStart_4118717 : Nat := 118140960795 + 4118717 * 2 ^ 59
def prefixEnd_4118717 : Nat := 4983230072969 + 3 ^ 40 * 4118717 * 2
def baseEnd_4118717 : Nat := 2114881500844267234495871

theorem tailTrace_4118717 : CollatzResearch.WordTrace tailWord_4118717 prefixEnd_4118717 2114881500844267234495871 := by
  unfold tailWord_4118717
  simp only [CollatzResearch.WordTrace]
  refine ⟨150221950219599204706514405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100147966813066136471009603 150221950219599204706514405)
  ·
    refine ⟨28166615666174850882471451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 150221950219599204706514405 28166615666174850882471451)
    ·
      refine ⟨42249923499262276323707177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28166615666174850882471451 42249923499262276323707177)
      ·
        refine ⟨31687442624446707242780383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42249923499262276323707177 31687442624446707242780383)
        ·
          refine ⟨47531163936670060864170575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31687442624446707242780383 47531163936670060864170575)
          ·
            refine ⟨71296745905005091296255863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47531163936670060864170575 71296745905005091296255863)
            ·
              refine ⟨106945118857507636944383795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71296745905005091296255863 106945118857507636944383795)
              ·
                refine ⟨160417678286261455416575693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 106945118857507636944383795 160417678286261455416575693)
                ·
                  refine ⟨60156629357348045781215885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 160417678286261455416575693 60156629357348045781215885)
                  ·
                    refine ⟨22558736009005517167955957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 60156629357348045781215885 22558736009005517167955957)
                    ·
                      refine ⟨2114881500844267234495871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22558736009005517167955957 2114881500844267234495871)
                      ·
                        rfl

theorem cell23_4118717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 1, 3, 3, 5].length) (baseStart_4118717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4118717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4118717 prefixEnd_4118717 := by exact prefixLift 4118717
  have htrace : WordTrace (prefixWord ++ tailWord_4118717) baseStart_4118717 baseEnd_4118717 := by
    simpa [prefixWord, tailWord_4118717, baseEnd_4118717] using wordTrace_append hprefix tailTrace_4118717
  have hstable : (prefixWord ++ tailWord_4118717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4118717).length < 2 ^ (prefixWord ++ tailWord_4118717).sum := by decide
  have hdescent : baseEnd_4118717 < baseStart_4118717 := by decide
  rcases family_descends (prefixWord ++ tailWord_4118717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4118734 : List Nat := [4, 1, 1, 1, 4, 1, 1, 2, 2, 1, 5]
def baseStart_4118734 : Nat := 118140960795 + 4118734 * 2 ^ 59
def prefixEnd_4118734 : Nat := 4983230072969 + 3 ^ 40 * 4118734 * 2
def baseEnd_4118734 : Nat := 2114890230015393667983293

theorem tailTrace_4118734 : CollatzResearch.WordTrace tailWord_4118734 prefixEnd_4118734 2114890230015393667983293 := by
  unfold tailWord_4118734
  simp only [CollatzResearch.WordTrace]
  refine ⟨18777821282567202076235407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 100148380173691744406588837 18777821282567202076235407)
  ·
    refine ⟨28166731923850803114353111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18777821282567202076235407 28166731923850803114353111)
    ·
      refine ⟨42250097885776204671529667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28166731923850803114353111 42250097885776204671529667)
      ·
        refine ⟨63375146828664307007294501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42250097885776204671529667 63375146828664307007294501)
        ·
          refine ⟨11882840030374557563867719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 63375146828664307007294501 11882840030374557563867719)
          ·
            refine ⟨17824260045561836345801579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11882840030374557563867719 17824260045561836345801579)
            ·
              refine ⟨26736390068342754518702369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17824260045561836345801579 26736390068342754518702369)
              ·
                refine ⟨20052292551257065889026777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26736390068342754518702369 20052292551257065889026777)
                ·
                  refine ⟨15039219413442799416770083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20052292551257065889026777 15039219413442799416770083)
                  ·
                    refine ⟨22558829120164199125155125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15039219413442799416770083 22558829120164199125155125)
                    ·
                      refine ⟨2114890230015393667983293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22558829120164199125155125 2114890230015393667983293)
                      ·
                        rfl

theorem cell23_4118734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 1, 2, 2, 1, 5].length) (baseStart_4118734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4118734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4118734 prefixEnd_4118734 := by exact prefixLift 4118734
  have htrace : WordTrace (prefixWord ++ tailWord_4118734) baseStart_4118734 baseEnd_4118734 := by
    simpa [prefixWord, tailWord_4118734, baseEnd_4118734] using wordTrace_append hprefix tailTrace_4118734
  have hstable : (prefixWord ++ tailWord_4118734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4118734).length < 2 ^ (prefixWord ++ tailWord_4118734).sum := by decide
  have hdescent : baseEnd_4118734 < baseStart_4118734 := by decide
  rcases family_descends (prefixWord ++ tailWord_4118734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4118737 : List Nat := [1, 2, 2, 1, 2, 2, 2, 4, 7]
def baseStart_4118737 : Nat := 118140960795 + 4118737 * 2 ^ 59
def prefixEnd_4118737 : Nat := 4983230072969 + 3 ^ 40 * 4118737 * 2
def baseEnd_4118737 : Nat := 234987974495261906249531

theorem tailTrace_4118737 : CollatzResearch.WordTrace tailWord_4118737 prefixEnd_4118737 234987974495261906249531 := by
  unfold tailWord_4118737
  simp only [CollatzResearch.WordTrace]
  refine ⟨150222679679526748122242465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100148453119684498748161643 150222679679526748122242465)
  ·
    refine ⟨112667009759645061091681849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150222679679526748122242465 112667009759645061091681849)
    ·
      refine ⟨84500257319733795818761387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112667009759645061091681849 84500257319733795818761387)
      ·
        refine ⟨126750385979600693728142081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84500257319733795818761387 126750385979600693728142081)
        ·
          refine ⟨95062789484700520296106561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126750385979600693728142081 95062789484700520296106561)
          ·
            refine ⟨71297092113525390222079921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95062789484700520296106561 71297092113525390222079921)
            ·
              refine ⟨53472819085144042666559941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71297092113525390222079921 53472819085144042666559941)
              ·
                refine ⟨10026153578464507999979989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53472819085144042666559941 10026153578464507999979989)
                ·
                  refine ⟨234987974495261906249531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10026153578464507999979989 234987974495261906249531)
                  ·
                    rfl

theorem cell23_4118737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 4, 7].length) (baseStart_4118737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4118737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4118737 prefixEnd_4118737 := by exact prefixLift 4118737
  have htrace : WordTrace (prefixWord ++ tailWord_4118737) baseStart_4118737 baseEnd_4118737 := by
    simpa [prefixWord, tailWord_4118737, baseEnd_4118737] using wordTrace_append hprefix tailTrace_4118737
  have hstable : (prefixWord ++ tailWord_4118737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4118737).length < 2 ^ (prefixWord ++ tailWord_4118737).sum := by decide
  have hdescent : baseEnd_4118737 < baseStart_4118737 := by decide
  rcases family_descends (prefixWord ++ tailWord_4118737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4118764 : List Nat := [2, 2, 1, 1, 2, 3, 2, 2, 2, 3, 3]
def baseStart_4118764 : Nat := 118140960795 + 4118764 * 2 ^ 59
def prefixEnd_4118764 : Nat := 4983230072969 + 3 ^ 40 * 4118764 * 2
def baseEnd_4118764 : Nat := 2114905634435028550608155

theorem tailTrace_4118764 : CollatzResearch.WordTrace tailWord_4118764 prefixEnd_4118764 2114905634435028550608155 := by
  unfold tailWord_4118764
  simp only [CollatzResearch.WordTrace]
  refine ⟨75111832225214465866737673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100149109633619287822316897 75111832225214465866737673)
  ·
    refine ⟨56333874168910849400053255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75111832225214465866737673 56333874168910849400053255)
    ·
      refine ⟨84500811253366274100079883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56333874168910849400053255 84500811253366274100079883)
      ·
        refine ⟨126751216880049411150119825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84500811253366274100079883 126751216880049411150119825)
        ·
          refine ⟨95063412660037058362589869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126751216880049411150119825 95063412660037058362589869)
          ·
            refine ⟨35648779747513896885971201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 95063412660037058362589869 35648779747513896885971201)
            ·
              refine ⟨26736584810635422664478401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35648779747513896885971201 26736584810635422664478401)
              ·
                refine ⟨20052438607976566998358801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26736584810635422664478401 20052438607976566998358801)
                ·
                  refine ⟨15039328955982425248769101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20052438607976566998358801 15039328955982425248769101)
                  ·
                    refine ⟨5639748358493409468288413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15039328955982425248769101 5639748358493409468288413)
                    ·
                      refine ⟨2114905634435028550608155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5639748358493409468288413 2114905634435028550608155)
                      ·
                        rfl

theorem cell23_4118764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 3, 3].length) (baseStart_4118764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4118764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4118764 prefixEnd_4118764 := by exact prefixLift 4118764
  have htrace : WordTrace (prefixWord ++ tailWord_4118764) baseStart_4118764 baseEnd_4118764 := by
    simpa [prefixWord, tailWord_4118764, baseEnd_4118764] using wordTrace_append hprefix tailTrace_4118764
  have hstable : (prefixWord ++ tailWord_4118764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4118764).length < 2 ^ (prefixWord ++ tailWord_4118764).sum := by decide
  have hdescent : baseEnd_4118764 < baseStart_4118764 := by decide
  rcases family_descends (prefixWord ++ tailWord_4118764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4118777 : List Nat := [1, 2, 1, 3, 1, 1, 2, 3, 1, 1, 7]
def baseStart_4118777 : Nat := 118140960795 + 4118777 * 2 ^ 59
def prefixEnd_4118777 : Nat := 4983230072969 + 3 ^ 40 * 4118777 * 2
def baseEnd_4118777 : Nat := 2114912309683536999745595

theorem tailTrace_4118777 : CollatzResearch.WordTrace tailWord_4118777 prefixEnd_4118777 2114912309683536999745595 := by
  unfold tailWord_4118777
  simp only [CollatzResearch.WordTrace]
  refine ⟨150224138599381834953698585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100149425732921223302465723 150224138599381834953698585)
  ·
    refine ⟨112668103949536376215273939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150224138599381834953698585 112668103949536376215273939)
    ·
      refine ⟨169002155924304564322910909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112668103949536376215273939 169002155924304564322910909)
      ·
        refine ⟨63375808471614211621091591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 169002155924304564322910909 63375808471614211621091591)
        ·
          refine ⟨95063712707421317431637387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63375808471614211621091591 95063712707421317431637387)
          ·
            refine ⟨142595569061131976147456081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95063712707421317431637387 142595569061131976147456081)
            ·
              refine ⟨106946676795848982110592061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 142595569061131976147456081 106946676795848982110592061)
              ·
                refine ⟨40105003798443368291472023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 106946676795848982110592061 40105003798443368291472023)
                ·
                  refine ⟨60157505697665052437208035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40105003798443368291472023 60157505697665052437208035)
                  ·
                    refine ⟨90236258546497578655812053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 60157505697665052437208035 90236258546497578655812053)
                    ·
                      refine ⟨2114912309683536999745595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 90236258546497578655812053 2114912309683536999745595)
                      ·
                        rfl

theorem cell23_4118777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 3, 1, 1, 7].length) (baseStart_4118777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4118777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4118777 prefixEnd_4118777 := by exact prefixLift 4118777
  have htrace : WordTrace (prefixWord ++ tailWord_4118777) baseStart_4118777 baseEnd_4118777 := by
    simpa [prefixWord, tailWord_4118777, baseEnd_4118777] using wordTrace_append hprefix tailTrace_4118777
  have hstable : (prefixWord ++ tailWord_4118777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4118777).length < 2 ^ (prefixWord ++ tailWord_4118777).sum := by decide
  have hdescent : baseEnd_4118777 < baseStart_4118777 := by decide
  rcases family_descends (prefixWord ++ tailWord_4118777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4118801 : List Nat := [1, 2, 2, 1, 1, 7, 1, 1, 2, 5]
def baseStart_4118801 : Nat := 118140960795 + 4118801 * 2 ^ 59
def prefixEnd_4118801 : Nat := 4983230072969 + 3 ^ 40 * 4118801 * 2
def baseEnd_4118801 : Nat := 704974877739748301948495

theorem tailTrace_4118801 : CollatzResearch.WordTrace tailWord_4118801 prefixEnd_4118801 704974877739748301948495 := by
  unfold tailWord_4118801
  simp only [CollatzResearch.WordTrace]
  refine ⟨150225013951294887052572257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100150009300863258035048171 150225013951294887052572257)
  ·
    refine ⟨112668760463471165289429193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150225013951294887052572257 112668760463471165289429193)
    ·
      refine ⟨84501570347603373967071895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112668760463471165289429193 84501570347603373967071895)
      ·
        refine ⟨126752355521405060950607843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84501570347603373967071895 126752355521405060950607843)
        ·
          refine ⟨190128533282107591425911765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126752355521405060950607843 190128533282107591425911765)
          ·
            refine ⟨4456137498799396674044807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 190128533282107591425911765 4456137498799396674044807)
            ·
              refine ⟨6684206248199095011067211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4456137498799396674044807 6684206248199095011067211)
              ·
                refine ⟨10026309372298642516600817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6684206248199095011067211 10026309372298642516600817)
                ·
                  refine ⟨7519732029223981887450613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10026309372298642516600817 7519732029223981887450613)
                  ·
                    refine ⟨704974877739748301948495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7519732029223981887450613 704974877739748301948495)
                    ·
                      rfl

theorem cell23_4118801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 7, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 7, 1, 1, 2, 5].length) (baseStart_4118801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4118801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4118801 prefixEnd_4118801 := by exact prefixLift 4118801
  have htrace : WordTrace (prefixWord ++ tailWord_4118801) baseStart_4118801 baseEnd_4118801 := by
    simpa [prefixWord, tailWord_4118801, baseEnd_4118801] using wordTrace_append hprefix tailTrace_4118801
  have hstable : (prefixWord ++ tailWord_4118801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4118801).length < 2 ^ (prefixWord ++ tailWord_4118801).sum := by decide
  have hdescent : baseEnd_4118801 < baseStart_4118801 := by decide
  rcases family_descends (prefixWord ++ tailWord_4118801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4118841 : List Nat := [1, 2, 1, 6, 1, 1, 1, 2, 1, 4, 3]
def baseStart_4118841 : Nat := 118140960795 + 4118841 * 2 ^ 59
def prefixEnd_4118841 : Nat := 4983230072969 + 3 ^ 40 * 4118841 * 2
def baseEnd_4118841 : Nat := 2114945172445424749345301

theorem tailTrace_4118841 : CollatzResearch.WordTrace tailWord_4118841 prefixEnd_4118841 2114945172445424749345301 := by
  unfold tailWord_4118841
  simp only [CollatzResearch.WordTrace]
  refine ⟨150226472871149973884028377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100150981914099982589352251 150226472871149973884028377)
  ·
    refine ⟨112669854653362480413021283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150226472871149973884028377 112669854653362480413021283)
    ·
      refine ⟨169004781980043720619531925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112669854653362480413021283 169004781980043720619531925)
      ·
        refine ⟨7922099155314549404040559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 169004781980043720619531925 7922099155314549404040559)
        ·
          refine ⟨11883148732971824106060839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7922099155314549404040559 11883148732971824106060839)
          ·
            refine ⟨17824723099457736159091259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11883148732971824106060839 17824723099457736159091259)
            ·
              refine ⟨26737084649186604238636889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17824723099457736159091259 26737084649186604238636889)
              ·
                refine ⟨20052813486889953178977667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26737084649186604238636889 20052813486889953178977667)
                ·
                  refine ⟨30079220230334929768466501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20052813486889953178977667 30079220230334929768466501)
                  ·
                    refine ⟨5639853793187799331587469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30079220230334929768466501 5639853793187799331587469)
                    ·
                      refine ⟨2114945172445424749345301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5639853793187799331587469 2114945172445424749345301)
                      ·
                        rfl

theorem cell23_4118841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 1, 2, 1, 4, 3].length) (baseStart_4118841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4118841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4118841 prefixEnd_4118841 := by exact prefixLift 4118841
  have htrace : WordTrace (prefixWord ++ tailWord_4118841) baseStart_4118841 baseEnd_4118841 := by
    simpa [prefixWord, tailWord_4118841, baseEnd_4118841] using wordTrace_append hprefix tailTrace_4118841
  have hstable : (prefixWord ++ tailWord_4118841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4118841).length < 2 ^ (prefixWord ++ tailWord_4118841).sum := by decide
  have hdescent : baseEnd_4118841 < baseStart_4118841 := by decide
  rcases family_descends (prefixWord ++ tailWord_4118841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4118865 : List Nat := [1, 2, 2, 1, 4, 4, 1, 3, 1, 4]
def baseStart_4118865 : Nat := 118140960795 + 4118865 * 2 ^ 59
def prefixEnd_4118865 : Nat := 4983230072969 + 3 ^ 40 * 4118865 * 2
def baseEnd_4118865 : Nat := 704985831993710885148397

theorem tailTrace_4118865 : CollatzResearch.WordTrace tailWord_4118865 prefixEnd_4118865 704985831993710885148397 := by
  unfold tailWord_4118865
  simp only [CollatzResearch.WordTrace]
  refine ⟨150227348223063025982902049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100151565482042017321934699 150227348223063025982902049)
  ·
    refine ⟨112670511167297269487176537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150227348223063025982902049 112670511167297269487176537)
    ·
      refine ⟨84502883375472952115382403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112670511167297269487176537 84502883375472952115382403)
      ·
        refine ⟨126754325063209428173073605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84502883375472952115382403 126754325063209428173073605)
        ·
          refine ⟨23766435949351767782451301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 126754325063209428173073605 23766435949351767782451301)
          ·
            refine ⟨4456206740503456459209619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23766435949351767782451301 4456206740503456459209619)
            ·
              refine ⟨6684310110755184688814429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4456206740503456459209619 6684310110755184688814429)
              ·
                refine ⟨2506616291533194258305411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6684310110755184688814429 2506616291533194258305411)
                ·
                  refine ⟨3759924437299791387458117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2506616291533194258305411 3759924437299791387458117)
                  ·
                    refine ⟨704985831993710885148397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3759924437299791387458117 704985831993710885148397)
                    ·
                      rfl

theorem cell23_4118865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 4, 1, 3, 1, 4].length) (baseStart_4118865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4118865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4118865 prefixEnd_4118865 := by exact prefixLift 4118865
  have htrace : WordTrace (prefixWord ++ tailWord_4118865) baseStart_4118865 baseEnd_4118865 := by
    simpa [prefixWord, tailWord_4118865, baseEnd_4118865] using wordTrace_append hprefix tailTrace_4118865
  have hstable : (prefixWord ++ tailWord_4118865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4118865).length < 2 ^ (prefixWord ++ tailWord_4118865).sum := by decide
  have hdescent : baseEnd_4118865 < baseStart_4118865 := by decide
  rcases family_descends (prefixWord ++ tailWord_4118865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4118874 : List Nat := [3, 1, 1, 2, 1, 2, 1, 2, 5, 5]
def baseStart_4118874 : Nat := 118140960795 + 4118874 * 2 ^ 59
def prefixEnd_4118874 : Nat := 4983230072969 + 3 ^ 40 * 4118874 * 2
def baseEnd_4118874 : Nat := 704987372435674373410883

theorem tailTrace_4118874 : CollatzResearch.WordTrace tailWord_4118874 prefixEnd_4118874 704987372435674373410883 := by
  unfold tailWord_4118874
  simp only [CollatzResearch.WordTrace]
  refine ⟨37556919120007605129994919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100151784320020280346653117 37556919120007605129994919)
  ·
    refine ⟨56335378680011407694992379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37556919120007605129994919 56335378680011407694992379)
    ·
      refine ⟨84503068020017111542488569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56335378680011407694992379 84503068020017111542488569)
      ·
        refine ⟨63377301015012833656866427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84503068020017111542488569 63377301015012833656866427)
        ·
          refine ⟨95065951522519250485299641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63377301015012833656866427 95065951522519250485299641)
          ·
            refine ⟨71299463641889437863974731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95065951522519250485299641 71299463641889437863974731)
            ·
              refine ⟨106949195462834156795962097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71299463641889437863974731 106949195462834156795962097)
              ·
                refine ⟨80211896597125617596971573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 106949195462834156795962097 80211896597125617596971573)
                ·
                  refine ⟨7519865305980526649716085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 80211896597125617596971573 7519865305980526649716085)
                  ·
                    refine ⟨704987372435674373410883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7519865305980526649716085 704987372435674373410883)
                    ·
                      rfl

theorem cell23_4118874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 2, 5, 5].length) (baseStart_4118874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4118874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4118874 prefixEnd_4118874 := by exact prefixLift 4118874
  have htrace : WordTrace (prefixWord ++ tailWord_4118874) baseStart_4118874 baseEnd_4118874 := by
    simpa [prefixWord, tailWord_4118874, baseEnd_4118874] using wordTrace_append hprefix tailTrace_4118874
  have hstable : (prefixWord ++ tailWord_4118874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4118874).length < 2 ^ (prefixWord ++ tailWord_4118874).sum := by decide
  have hdescent : baseEnd_4118874 < baseStart_4118874 := by decide
  rcases family_descends (prefixWord ++ tailWord_4118874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4118882 : List Nat := [3, 3, 2, 1, 1, 3, 3, 2, 1, 4]
def baseStart_4118882 : Nat := 118140960795 + 4118882 * 2 ^ 59
def prefixEnd_4118882 : Nat := 4983230072969 + 3 ^ 40 * 4118882 * 2
def baseEnd_4118882 : Nat := 704988741717419696310871

theorem tailTrace_4118882 : CollatzResearch.WordTrace tailWord_4118882 prefixEnd_4118882 704988741717419696310871 := by
  unfold tailWord_4118882
  simp only [CollatzResearch.WordTrace]
  refine ⟨37556992066000359471567725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100151978842667625257513933 37556992066000359471567725)
  ·
    refine ⟨14083872024750134801837897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37556992066000359471567725 14083872024750134801837897)
    ·
      refine ⟨10562904018562601101378423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14083872024750134801837897 10562904018562601101378423)
      ·
        refine ⟨15844356027843901652067635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10562904018562601101378423 15844356027843901652067635)
        ·
          refine ⟨23766534041765852478101453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15844356027843901652067635 23766534041765852478101453)
          ·
            refine ⟨8912450265662194679288045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23766534041765852478101453 8912450265662194679288045)
            ·
              refine ⟨3342168849623323004733017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8912450265662194679288045 3342168849623323004733017)
              ·
                refine ⟨2506626637217492253549763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3342168849623323004733017 2506626637217492253549763)
                ·
                  refine ⟨3759939955826238380324645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2506626637217492253549763 3759939955826238380324645)
                  ·
                    refine ⟨704988741717419696310871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3759939955826238380324645 704988741717419696310871)
                    ·
                      rfl

theorem cell23_4118882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 3, 2, 1, 4].length) (baseStart_4118882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4118882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4118882 prefixEnd_4118882 := by exact prefixLift 4118882
  have htrace : WordTrace (prefixWord ++ tailWord_4118882) baseStart_4118882 baseEnd_4118882 := by
    simpa [prefixWord, tailWord_4118882, baseEnd_4118882] using wordTrace_append hprefix tailTrace_4118882
  have hstable : (prefixWord ++ tailWord_4118882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4118882).length < 2 ^ (prefixWord ++ tailWord_4118882).sum := by decide
  have hdescent : baseEnd_4118882 < baseStart_4118882 := by decide
  rcases family_descends (prefixWord ++ tailWord_4118882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4118915 : List Nat := [1, 1, 1, 3, 6, 1, 2, 1, 2, 3, 2]
def baseStart_4118915 : Nat := 118140960795 + 4118915 * 2 ^ 59
def prefixEnd_4118915 : Nat := 4983230072969 + 3 ^ 40 * 4118915 * 2
def baseEnd_4118915 : Nat := 2114983170013857459819961

theorem tailTrace_4118915 : CollatzResearch.WordTrace tailWord_4118915 prefixEnd_4118915 2114983170013857459819961 := by
  unfold tailWord_4118915
  simp only [CollatzResearch.WordTrace]
  refine ⟨150229171872881884522222199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100152781248587923014814799 150229171872881884522222199)
  ·
    refine ⟨225343757809322826783333299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150229171872881884522222199 225343757809322826783333299)
    ·
      refine ⟨338015636713984240174999949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225343757809322826783333299 338015636713984240174999949)
      ·
        refine ⟨126755863767744090065624981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 338015636713984240174999949 126755863767744090065624981)
        ·
          refine ⟨5941681114113004221826171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 126755863767744090065624981 5941681114113004221826171)
          ·
            refine ⟨8912521671169506332739257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5941681114113004221826171 8912521671169506332739257)
            ·
              refine ⟨6684391253377129749554443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8912521671169506332739257 6684391253377129749554443)
              ·
                refine ⟨10026586880065694624331665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6684391253377129749554443 10026586880065694624331665)
                ·
                  refine ⟨7519940160049270968248749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10026586880065694624331665 7519940160049270968248749)
                  ·
                    refine ⟨2819977560018476613093281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7519940160049270968248749 2819977560018476613093281)
                    ·
                      refine ⟨2114983170013857459819961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2819977560018476613093281 2114983170013857459819961)
                      ·
                        rfl

theorem cell23_4118915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 2, 1, 2, 3, 2].length) (baseStart_4118915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4118915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4118915 prefixEnd_4118915 := by exact prefixLift 4118915
  have htrace : WordTrace (prefixWord ++ tailWord_4118915) baseStart_4118915 baseEnd_4118915 := by
    simpa [prefixWord, tailWord_4118915, baseEnd_4118915] using wordTrace_append hprefix tailTrace_4118915
  have hstable : (prefixWord ++ tailWord_4118915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4118915).length < 2 ^ (prefixWord ++ tailWord_4118915).sum := by decide
  have hdescent : baseEnd_4118915 < baseStart_4118915 := by decide
  rcases family_descends (prefixWord ++ tailWord_4118915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4118921 : List Nat := [1, 2, 1, 1, 6, 2, 1, 2, 1, 6]
def baseStart_4118921 : Nat := 118140960795 + 4118921 * 2 ^ 59
def prefixEnd_4118921 : Nat := 4983230072969 + 3 ^ 40 * 4118921 * 2
def baseEnd_4118921 : Nat := 704995416965928145448311

theorem tailTrace_4118921 : CollatzResearch.WordTrace tailWord_4118921 prefixEnd_4118921 704995416965928145448311 := by
  unfold tailWord_4118921
  simp only [CollatzResearch.WordTrace]
  refine ⟨150229390710860147546940617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100152927140573431697960411 150229390710860147546940617)
  ·
    refine ⟨112672043033145110660205463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150229390710860147546940617 112672043033145110660205463)
    ·
      refine ⟨169008064549717665990308195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112672043033145110660205463 169008064549717665990308195)
      ·
        refine ⟨253512096824576498985462293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169008064549717665990308195 253512096824576498985462293)
        ·
          refine ⟨11883379538652023389943545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 253512096824576498985462293 11883379538652023389943545)
          ·
            refine ⟨8912534653989017542457659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11883379538652023389943545 8912534653989017542457659)
            ·
              refine ⟨13368801980983526313686489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8912534653989017542457659 13368801980983526313686489)
              ·
                refine ⟨10026601485737644735264867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13368801980983526313686489 10026601485737644735264867)
                ·
                  refine ⟨15039902228606467102897301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10026601485737644735264867 15039902228606467102897301)
                  ·
                    refine ⟨704995416965928145448311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15039902228606467102897301 704995416965928145448311)
                    ·
                      rfl

theorem cell23_4118921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 1, 2, 1, 6].length) (baseStart_4118921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4118921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4118921 prefixEnd_4118921 := by exact prefixLift 4118921
  have htrace : WordTrace (prefixWord ++ tailWord_4118921) baseStart_4118921 baseEnd_4118921 := by
    simpa [prefixWord, tailWord_4118921, baseEnd_4118921] using wordTrace_append hprefix tailTrace_4118921
  have hstable : (prefixWord ++ tailWord_4118921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4118921).length < 2 ^ (prefixWord ++ tailWord_4118921).sum := by decide
  have hdescent : baseEnd_4118921 < baseStart_4118921 := by decide
  rcases family_descends (prefixWord ++ tailWord_4118921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4118938 : List Nat := [3, 1, 1, 4, 1, 2, 1, 4, 2, 4]
def baseStart_4118938 : Nat := 118140960795 + 4118938 * 2 ^ 59
def prefixEnd_4118938 : Nat := 4983230072969 + 3 ^ 40 * 4118938 * 2
def baseEnd_4118938 : Nat := 704998326689636956610785

theorem tailTrace_4118938 : CollatzResearch.WordTrace tailWord_4118938 prefixEnd_4118938 704998326689636956610785 := by
  unfold tailWord_4118938
  simp only [CollatzResearch.WordTrace]
  refine ⟨37557502687949639862577367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100153340501199039633539645 37557502687949639862577367)
  ·
    refine ⟨56336254031924459793866051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37557502687949639862577367 56336254031924459793866051)
    ·
      refine ⟨84504381047886689690799077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56336254031924459793866051 84504381047886689690799077)
      ·
        refine ⟨15844571446478754317024827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 84504381047886689690799077 15844571446478754317024827)
        ·
          refine ⟨23766857169718131475537241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15844571446478754317024827 23766857169718131475537241)
          ·
            refine ⟨17825142877288598606652931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23766857169718131475537241 17825142877288598606652931)
            ·
              refine ⟨26737714315932897909979397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17825142877288598606652931 26737714315932897909979397)
              ·
                refine ⟨5013321434237418358121137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26737714315932897909979397 5013321434237418358121137)
                ·
                  refine ⟨3759991075678063768590853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5013321434237418358121137 3759991075678063768590853)
                  ·
                    refine ⟨704998326689636956610785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3759991075678063768590853 704998326689636956610785)
                    ·
                      rfl

theorem cell23_4118938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 1, 4, 2, 4].length) (baseStart_4118938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4118938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4118938 prefixEnd_4118938 := by exact prefixLift 4118938
  have htrace : WordTrace (prefixWord ++ tailWord_4118938) baseStart_4118938 baseEnd_4118938 := by
    simpa [prefixWord, tailWord_4118938, baseEnd_4118938] using wordTrace_append hprefix tailTrace_4118938
  have hstable : (prefixWord ++ tailWord_4118938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4118938).length < 2 ^ (prefixWord ++ tailWord_4118938).sum := by decide
  have hdescent : baseEnd_4118938 < baseStart_4118938 := by decide
  rcases family_descends (prefixWord ++ tailWord_4118938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4118951 : List Nat := [1, 1, 6, 1, 1, 2, 3, 8]
def baseStart_4118951 : Nat := 118140960795 + 4118951 * 2 ^ 59
def prefixEnd_4118951 : Nat := 4983230072969 + 3 ^ 40 * 4118951 * 2
def baseEnd_4118951 : Nat := 78333394641385900702585

theorem tailTrace_4118951 : CollatzResearch.WordTrace tailWord_4118951 prefixEnd_4118951 78333394641385900702585 := by
  unfold tailWord_4118951
  simp only [CollatzResearch.WordTrace]
  refine ⟨150230484900751462670532707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100153656600500975113688471 150230484900751462670532707)
  ·
    refine ⟨225345727351127194005799061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150230484900751462670532707 225345727351127194005799061)
    ·
      refine ⟨10563080969584087219021831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 225345727351127194005799061 10563080969584087219021831)
      ·
        refine ⟨15844621454376130828532747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10563080969584087219021831 15844621454376130828532747)
        ·
          refine ⟨23766932181564196242799121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15844621454376130828532747 23766932181564196242799121)
          ·
            refine ⟨17825199136173147182099341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23766932181564196242799121 17825199136173147182099341)
            ·
              refine ⟨6684449676064930193287253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17825199136173147182099341 6684449676064930193287253)
              ·
                refine ⟨78333394641385900702585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6684449676064930193287253 78333394641385900702585)
                ·
                  rfl

theorem cell23_4118951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 3, 8].length) (baseStart_4118951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4118951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4118951 prefixEnd_4118951 := by exact prefixLift 4118951
  have htrace : WordTrace (prefixWord ++ tailWord_4118951) baseStart_4118951 baseEnd_4118951 := by
    simpa [prefixWord, tailWord_4118951, baseEnd_4118951] using wordTrace_append hprefix tailTrace_4118951
  have hstable : (prefixWord ++ tailWord_4118951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4118951).length < 2 ^ (prefixWord ++ tailWord_4118951).sum := by decide
  have hdescent : baseEnd_4118951 < baseStart_4118951 := by decide
  rcases family_descends (prefixWord ++ tailWord_4118951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4118971 : List Nat := [1, 1, 1, 1, 1, 2, 2, 1, 4, 7, 2]
def baseStart_4118971 : Nat := 118140960795 + 4118971 * 2 ^ 59
def prefixEnd_4118971 : Nat := 4983230072969 + 3 ^ 40 * 4118971 * 2
def baseEnd_4118971 : Nat := 2115011924930509240719703

theorem tailTrace_4118971 : CollatzResearch.WordTrace tailWord_4118971 prefixEnd_4118971 2115011924930509240719703 := by
  unfold tailWord_4118971
  simp only [CollatzResearch.WordTrace]
  refine ⟨150231214360679006086260767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100154142907119337390840511 150231214360679006086260767)
  ·
    refine ⟨225346821541018509129391151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150231214360679006086260767 225346821541018509129391151)
    ·
      refine ⟨338020232311527763694086727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225346821541018509129391151 338020232311527763694086727)
      ·
        refine ⟨507030348467291645541130091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 338020232311527763694086727 507030348467291645541130091)
        ·
          refine ⟨760545522700937468311695137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 507030348467291645541130091 760545522700937468311695137)
          ·
            refine ⟨570409142025703101233771353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 760545522700937468311695137 570409142025703101233771353)
            ·
              refine ⟨427806856519277325925328515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 570409142025703101233771353 427806856519277325925328515)
              ·
                refine ⟨641710284778915988887992773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 427806856519277325925328515 641710284778915988887992773)
                ·
                  refine ⟨120320678396046747916498645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 641710284778915988887992773 120320678396046747916498645)
                  ·
                    refine ⟨2820015899907345654292937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 120320678396046747916498645 2820015899907345654292937)
                    ·
                      refine ⟨2115011924930509240719703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2820015899907345654292937 2115011924930509240719703)
                      ·
                        rfl

theorem cell23_4118971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 4, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 4, 7, 2].length) (baseStart_4118971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4118971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4118971 prefixEnd_4118971 := by exact prefixLift 4118971
  have htrace : WordTrace (prefixWord ++ tailWord_4118971) baseStart_4118971 baseEnd_4118971 := by
    simpa [prefixWord, tailWord_4118971, baseEnd_4118971] using wordTrace_append hprefix tailTrace_4118971
  have hstable : (prefixWord ++ tailWord_4118971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4118971).length < 2 ^ (prefixWord ++ tailWord_4118971).sum := by decide
  have hdescent : baseEnd_4118971 < baseStart_4118971 := by decide
  rcases family_descends (prefixWord ++ tailWord_4118971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4119022 : List Nat := [4, 1, 2, 1, 2, 3, 2, 2, 1, 3, 2]
def baseStart_4119022 : Nat := 118140960795 + 4119022 * 2 ^ 59
def prefixEnd_4119022 : Nat := 4983230072969 + 3 ^ 40 * 4119022 * 2
def baseEnd_4119022 : Nat := 2115038112443888541181969

theorem tailTrace_4119022 : CollatzResearch.WordTrace tailWord_4119022 prefixEnd_4119022 2115038112443888541181969 := by
  unfold tailWord_4119022
  simp only [CollatzResearch.WordTrace]
  refine ⟨18779134310436780224545915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 100155382988996161197578213 18779134310436780224545915)
  ·
    refine ⟨28168701465655170336818873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18779134310436780224545915 28168701465655170336818873)
    ·
      refine ⟨21126526099241377752614155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28168701465655170336818873 21126526099241377752614155)
      ·
        refine ⟨31689789148862066628921233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21126526099241377752614155 31689789148862066628921233)
        ·
          refine ⟨23767341861646549971690925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31689789148862066628921233 23767341861646549971690925)
          ·
            refine ⟨8912753198117456239384097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23767341861646549971690925 8912753198117456239384097)
            ·
              refine ⟨6684564898588092179538073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8912753198117456239384097 6684564898588092179538073)
              ·
                refine ⟨5013423673941069134653555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6684564898588092179538073 5013423673941069134653555)
                ·
                  refine ⟨7520135510911603701980333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5013423673941069134653555 7520135510911603701980333)
                  ·
                    refine ⟨2820050816591851388242625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7520135510911603701980333 2820050816591851388242625)
                    ·
                      refine ⟨2115038112443888541181969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2820050816591851388242625 2115038112443888541181969)
                      ·
                        rfl

theorem cell23_4119022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 2, 2, 1, 3, 2].length) (baseStart_4119022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4119022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4119022 prefixEnd_4119022 := by exact prefixLift 4119022
  have htrace : WordTrace (prefixWord ++ tailWord_4119022) baseStart_4119022 baseEnd_4119022 := by
    simpa [prefixWord, tailWord_4119022, baseEnd_4119022] using wordTrace_append hprefix tailTrace_4119022
  have hstable : (prefixWord ++ tailWord_4119022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4119022).length < 2 ^ (prefixWord ++ tailWord_4119022).sum := by decide
  have hdescent : baseEnd_4119022 < baseStart_4119022 := by decide
  rcases family_descends (prefixWord ++ tailWord_4119022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4119069 : List Nat := [1, 4, 2, 2, 1, 2, 4, 1, 2, 2, 2]
def baseStart_4119069 : Nat := 118140960795 + 4119069 * 2 ^ 59
def prefixEnd_4119069 : Nat := 4983230072969 + 3 ^ 40 * 4119069 * 2
def baseEnd_4119069 : Nat := 2115062246034649857294253

theorem tailTrace_4119069 : CollatzResearch.WordTrace tailWord_4119069 prefixEnd_4119069 2115062246034649857294253 := by
  unfold tailWord_4119069
  simp only [CollatzResearch.WordTrace]
  refine ⟨150234788714323968823328261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100156525809549312548885507 150234788714323968823328261)
  ·
    refine ⟨28169022883935744154374049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 150234788714323968823328261 28169022883935744154374049)
    ·
      refine ⟨21126767162951808115780537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28169022883935744154374049 21126767162951808115780537)
      ·
        refine ⟨15845075372213856086835403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21126767162951808115780537 15845075372213856086835403)
        ·
          refine ⟨23767613058320784130253105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15845075372213856086835403 23767613058320784130253105)
          ·
            refine ⟨17825709793740588097689829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23767613058320784130253105 17825709793740588097689829)
            ·
              refine ⟨3342320586326360268316843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17825709793740588097689829 3342320586326360268316843)
              ·
                refine ⟨5013480879489540402475265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3342320586326360268316843 5013480879489540402475265)
                ·
                  refine ⟨3760110659617155301856449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5013480879489540402475265 3760110659617155301856449)
                  ·
                    refine ⟨2820082994712866476392337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3760110659617155301856449 2820082994712866476392337)
                    ·
                      refine ⟨2115062246034649857294253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2820082994712866476392337 2115062246034649857294253)
                      ·
                        rfl

theorem cell23_4119069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 4, 1, 2, 2, 2].length) (baseStart_4119069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4119069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4119069 prefixEnd_4119069 := by exact prefixLift 4119069
  have htrace : WordTrace (prefixWord ++ tailWord_4119069) baseStart_4119069 baseEnd_4119069 := by
    simpa [prefixWord, tailWord_4119069, baseEnd_4119069] using wordTrace_append hprefix tailTrace_4119069
  have hstable : (prefixWord ++ tailWord_4119069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4119069).length < 2 ^ (prefixWord ++ tailWord_4119069).sum := by decide
  have hdescent : baseEnd_4119069 < baseStart_4119069 := by decide
  rcases family_descends (prefixWord ++ tailWord_4119069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4119071 : List Nat := [1, 1, 2, 4, 1, 1, 1, 1, 6, 5]
def baseStart_4119071 : Nat := 118140960795 + 4119071 * 2 ^ 59
def prefixEnd_4119071 : Nat := 4983230072969 + 3 ^ 40 * 4119071 * 2
def baseEnd_4119071 : Nat := 705021090998652949823081

theorem tailTrace_4119071 : CollatzResearch.WordTrace tailWord_4119071 prefixEnd_4119071 705021090998652949823081 := by
  unfold tailWord_4119071
  simp only [CollatzResearch.WordTrace]
  refine ⟨150234861660316723164901067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100156574440211148776600711 150234861660316723164901067)
  ·
    refine ⟨225352292490475084747351601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150234861660316723164901067 225352292490475084747351601)
    ·
      refine ⟨169014219367856313560513701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 225352292490475084747351601 169014219367856313560513701)
      ·
        refine ⟨31690166131473058792596319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 169014219367856313560513701 31690166131473058792596319)
        ·
          refine ⟨47535249197209588188894479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31690166131473058792596319 47535249197209588188894479)
          ·
            refine ⟨71302873795814382283341719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47535249197209588188894479 71302873795814382283341719)
            ·
              refine ⟨106954310693721573425012579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71302873795814382283341719 106954310693721573425012579)
              ·
                refine ⟨160431466040582360137518869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 106954310693721573425012579 160431466040582360137518869)
                ·
                  refine ⟨7520224970652298131446197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 160431466040582360137518869 7520224970652298131446197)
                  ·
                    refine ⟨705021090998652949823081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7520224970652298131446197 705021090998652949823081)
                    ·
                      rfl

theorem cell23_4119071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 1, 6, 5].length) (baseStart_4119071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4119071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4119071 prefixEnd_4119071 := by exact prefixLift 4119071
  have htrace : WordTrace (prefixWord ++ tailWord_4119071) baseStart_4119071 baseEnd_4119071 := by
    simpa [prefixWord, tailWord_4119071, baseEnd_4119071] using wordTrace_append hprefix tailTrace_4119071
  have hstable : (prefixWord ++ tailWord_4119071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4119071).length < 2 ^ (prefixWord ++ tailWord_4119071).sum := by decide
  have hdescent : baseEnd_4119071 < baseStart_4119071 := by decide
  rcases family_descends (prefixWord ++ tailWord_4119071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4119128 : List Nat := [2, 1, 2, 2, 1, 2, 2, 2, 4, 2, 3]
def baseStart_4119128 : Nat := 118140960795 + 4119128 * 2 ^ 59
def prefixEnd_4119128 : Nat := 4983230072969 + 3 ^ 40 * 4119128 * 2
def baseEnd_4119128 : Nat := 2115092541393265126456481

theorem tailTrace_4119128 : CollatzResearch.WordTrace tailWord_4119128 prefixEnd_4119128 2115092541393265126456481 := by
  unfold tailWord_4119128
  simp only [CollatzResearch.WordTrace]
  refine ⟨75118470310555110949863019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100157960414073481266484025 75118470310555110949863019)
  ·
    refine ⟨112677705465832666424794529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75118470310555110949863019 112677705465832666424794529)
    ·
      refine ⟨84508279099374499818595897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112677705465832666424794529 84508279099374499818595897)
      ·
        refine ⟨63381209324530874863946923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84508279099374499818595897 63381209324530874863946923)
        ·
          refine ⟨95071813986796312295920385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63381209324530874863946923 95071813986796312295920385)
          ·
            refine ⟨71303860490097234221940289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95071813986796312295920385 71303860490097234221940289)
            ·
              refine ⟨53477895367572925666455217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71303860490097234221940289 53477895367572925666455217)
              ·
                refine ⟨40108421525679694249841413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53477895367572925666455217 40108421525679694249841413)
                ·
                  refine ⟨7520329036064942671845265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40108421525679694249841413 7520329036064942671845265)
                  ·
                    refine ⟨5640246777048707003883949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7520329036064942671845265 5640246777048707003883949)
                    ·
                      refine ⟨2115092541393265126456481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5640246777048707003883949 2115092541393265126456481)
                      ·
                        rfl

theorem cell23_4119128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 2, 4, 2, 3].length) (baseStart_4119128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4119128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4119128 prefixEnd_4119128 := by exact prefixLift 4119128
  have htrace : WordTrace (prefixWord ++ tailWord_4119128) baseStart_4119128 baseEnd_4119128 := by
    simpa [prefixWord, tailWord_4119128, baseEnd_4119128] using wordTrace_append hprefix tailTrace_4119128
  have hstable : (prefixWord ++ tailWord_4119128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4119128).length < 2 ^ (prefixWord ++ tailWord_4119128).sum := by decide
  have hdescent : baseEnd_4119128 < baseStart_4119128 := by decide
  rcases family_descends (prefixWord ++ tailWord_4119128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4119215 : List Nat := [1, 1, 2, 1, 2, 5, 2, 3, 1, 1, 4]
def baseStart_4119215 : Nat := 118140960795 + 4119215 * 2 ^ 59
def prefixEnd_4119215 : Nat := 4983230072969 + 3 ^ 40 * 4119215 * 2
def baseEnd_4119215 : Nat := 2115137214210206286068581

theorem tailTrace_4119215 : CollatzResearch.WordTrace tailWord_4119215 prefixEnd_4119215 2115137214210206286068581 := by
  unfold tailWord_4119215
  simp only [CollatzResearch.WordTrace]
  refine ⟨150240113771795035758143099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100160075847863357172095399 150240113771795035758143099)
  ·
    refine ⟨225360170657692553637214649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150240113771795035758143099 225360170657692553637214649)
    ·
      refine ⟨169020127993269415227910987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 225360170657692553637214649 169020127993269415227910987)
      ·
        refine ⟨253530191989904122841866481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169020127993269415227910987 253530191989904122841866481)
        ·
          refine ⟨190147643992428092131399861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 253530191989904122841866481 190147643992428092131399861)
          ·
            refine ⟨17826341624290133637318737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 190147643992428092131399861 17826341624290133637318737)
            ·
              refine ⟨13369756218217600227989053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17826341624290133637318737 13369756218217600227989053)
              ·
                refine ⟨5013658581831600085495895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13369756218217600227989053 5013658581831600085495895)
                ·
                  refine ⟨7520487872747400128243843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5013658581831600085495895 7520487872747400128243843)
                  ·
                    refine ⟨11280731809121100192365765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7520487872747400128243843 11280731809121100192365765)
                    ·
                      refine ⟨2115137214210206286068581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11280731809121100192365765 2115137214210206286068581)
                      ·
                        rfl

theorem cell23_4119215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 2, 3, 1, 1, 4].length) (baseStart_4119215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4119215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4119215 prefixEnd_4119215 := by exact prefixLift 4119215
  have htrace : WordTrace (prefixWord ++ tailWord_4119215) baseStart_4119215 baseEnd_4119215 := by
    simpa [prefixWord, tailWord_4119215, baseEnd_4119215] using wordTrace_append hprefix tailTrace_4119215
  have hstable : (prefixWord ++ tailWord_4119215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4119215).length < 2 ^ (prefixWord ++ tailWord_4119215).sum := by decide
  have hdescent : baseEnd_4119215 < baseStart_4119215 := by decide
  rcases family_descends (prefixWord ++ tailWord_4119215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4119225 : List Nat := [1, 2, 1, 4, 1, 1, 1, 6, 2, 4]
def baseStart_4119225 : Nat := 118140960795 + 4119225 * 2 ^ 59
def prefixEnd_4119225 : Nat := 4983230072969 + 3 ^ 40 * 4119225 * 2
def baseEnd_4119225 : Nat := 705047449672250415647845

theorem tailTrace_4119225 : CollatzResearch.WordTrace tailWord_4119225 prefixEnd_4119225 705047449672250415647845 := by
  unfold tailWord_4119225
  simp only [CollatzResearch.WordTrace]
  refine ⟨150240478501758807466007129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100160319001172538310671419 150240478501758807466007129)
  ·
    refine ⟨112680358876319105599505347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150240478501758807466007129 112680358876319105599505347)
    ·
      refine ⟨169020538314478658399258021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112680358876319105599505347 169020538314478658399258021)
      ·
        refine ⟨31691350933964748449860879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 169020538314478658399258021 31691350933964748449860879)
        ·
          refine ⟨47537026400947122674791319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31691350933964748449860879 47537026400947122674791319)
          ·
            refine ⟨71305539601420684012186979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47537026400947122674791319 71305539601420684012186979)
            ·
              refine ⟨106958309402131026018280469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71305539601420684012186979 106958309402131026018280469)
              ·
                refine ⟨5013670753224891844606897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 106958309402131026018280469 5013670753224891844606897)
                ·
                  refine ⟨3760253064918668883455173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5013670753224891844606897 3760253064918668883455173)
                  ·
                    refine ⟨705047449672250415647845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3760253064918668883455173 705047449672250415647845)
                    ·
                      rfl

theorem cell23_4119225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 6, 2, 4].length) (baseStart_4119225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4119225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4119225 prefixEnd_4119225 := by exact prefixLift 4119225
  have htrace : WordTrace (prefixWord ++ tailWord_4119225) baseStart_4119225 baseEnd_4119225 := by
    simpa [prefixWord, tailWord_4119225, baseEnd_4119225] using wordTrace_append hprefix tailTrace_4119225
  have hstable : (prefixWord ++ tailWord_4119225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4119225).length < 2 ^ (prefixWord ++ tailWord_4119225).sum := by decide
  have hdescent : baseEnd_4119225 < baseStart_4119225 := by decide
  rcases family_descends (prefixWord ++ tailWord_4119225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4119228 : List Nat := [2, 2, 2, 3, 1, 1, 1, 1, 3, 1, 6]
def baseStart_4119228 : Nat := 118140960795 + 4119228 * 2 ^ 59
def prefixEnd_4119228 : Nat := 4983230072969 + 3 ^ 40 * 4119228 * 2
def baseEnd_4119228 : Nat := 2115143889458714735206021

theorem tailTrace_4119228 : CollatzResearch.WordTrace tailWord_4119228 prefixEnd_4119228 2115143889458714735206021 := by
  unfold tailWord_4119228
  simp only [CollatzResearch.WordTrace]
  refine ⟨75120293960373969489183169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100160391947165292652244225 75120293960373969489183169)
  ·
    refine ⟨56340220470280477116887377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75120293960373969489183169 56340220470280477116887377)
    ·
      refine ⟨42255165352710357837665533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56340220470280477116887377 42255165352710357837665533)
      ·
        refine ⟨15845687007266384189124575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42255165352710357837665533 15845687007266384189124575)
        ·
          refine ⟨23768530510899576283686863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15845687007266384189124575 23768530510899576283686863)
          ·
            refine ⟨35652795766349364425530295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23768530510899576283686863 35652795766349364425530295)
            ·
              refine ⟨53479193649524046638295443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35652795766349364425530295 53479193649524046638295443)
              ·
                refine ⟨80218790474286069957443165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53479193649524046638295443 80218790474286069957443165)
                ·
                  refine ⟨30082046427857276234041187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 80218790474286069957443165 30082046427857276234041187)
                  ·
                    refine ⟨45123069641785914351061781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30082046427857276234041187 45123069641785914351061781)
                    ·
                      refine ⟨2115143889458714735206021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 45123069641785914351061781 2115143889458714735206021)
                      ·
                        rfl

theorem cell23_4119228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 1, 3, 1, 6].length) (baseStart_4119228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4119228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4119228 prefixEnd_4119228 := by exact prefixLift 4119228
  have htrace : WordTrace (prefixWord ++ tailWord_4119228) baseStart_4119228 baseEnd_4119228 := by
    simpa [prefixWord, tailWord_4119228, baseEnd_4119228] using wordTrace_append hprefix tailTrace_4119228
  have hstable : (prefixWord ++ tailWord_4119228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4119228).length < 2 ^ (prefixWord ++ tailWord_4119228).sum := by decide
  have hdescent : baseEnd_4119228 < baseStart_4119228 := by decide
  rcases family_descends (prefixWord ++ tailWord_4119228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4119242 : List Nat := [3, 1, 2, 1, 4, 2, 1, 3, 2, 4]
def baseStart_4119242 : Nat := 118140960795 + 4119242 * 2 ^ 59
def prefixEnd_4119242 : Nat := 4983230072969 + 3 ^ 40 * 4119242 * 2
def baseEnd_4119242 : Nat := 705050359395959226810319

theorem tailTrace_4119242 : CollatzResearch.WordTrace tailWord_4119242 prefixEnd_4119242 705050359395959226810319 := by
  unfold tailWord_4119242
  simp only [CollatzResearch.WordTrace]
  refine ⟨37560274635674304842343995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100160732361798146246250653 37560274635674304842343995)
  ·
    refine ⟨56340411953511457263515993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37560274635674304842343995 56340411953511457263515993)
    ·
      refine ⟨42255308965133592947636995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56340411953511457263515993 42255308965133592947636995)
      ·
        refine ⟨63382963447700389421455493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42255308965133592947636995 63382963447700389421455493)
        ·
          refine ⟨11884305646443823016522905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 63382963447700389421455493 11884305646443823016522905)
          ·
            refine ⟨8913229234832867262392179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11884305646443823016522905 8913229234832867262392179)
            ·
              refine ⟨13369843852249300893588269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8913229234832867262392179 13369843852249300893588269)
              ·
                refine ⟨5013691444593487835095601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13369843852249300893588269 5013691444593487835095601)
                ·
                  refine ⟨3760268583445115876321701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5013691444593487835095601 3760268583445115876321701)
                  ·
                    refine ⟨705050359395959226810319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3760268583445115876321701 705050359395959226810319)
                    ·
                      rfl

theorem cell23_4119242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 1, 3, 2, 4].length) (baseStart_4119242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4119242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4119242 prefixEnd_4119242 := by exact prefixLift 4119242
  have htrace : WordTrace (prefixWord ++ tailWord_4119242) baseStart_4119242 baseEnd_4119242 := by
    simpa [prefixWord, tailWord_4119242, baseEnd_4119242] using wordTrace_append hprefix tailTrace_4119242
  have hstable : (prefixWord ++ tailWord_4119242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4119242).length < 2 ^ (prefixWord ++ tailWord_4119242).sum := by decide
  have hdescent : baseEnd_4119242 < baseStart_4119242 := by decide
  rcases family_descends (prefixWord ++ tailWord_4119242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4119265 : List Nat := [1, 2, 3, 1, 4, 1, 1, 1, 3, 3, 3]
def baseStart_4119265 : Nat := 118140960795 + 4119265 * 2 ^ 59
def prefixEnd_4119265 : Nat := 4983230072969 + 3 ^ 40 * 4119265 * 2
def baseEnd_4119265 : Nat := 2115162888242931090443351

theorem tailTrace_4119265 : CollatzResearch.WordTrace tailWord_4119265 prefixEnd_4119265 2115162888242931090443351 := by
  unfold tailWord_4119265
  simp only [CollatzResearch.WordTrace]
  refine ⟨150241937421613894297463249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100161291614409262864975499 150241937421613894297463249)
  ·
    refine ⟨112681453066210420723097437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150241937421613894297463249 112681453066210420723097437)
    ·
      refine ⟨42255544899828907771161539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 112681453066210420723097437 42255544899828907771161539)
      ·
        refine ⟨63383317349743361656742309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42255544899828907771161539 63383317349743361656742309)
        ·
          refine ⟨11884372003076880310639183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 63383317349743361656742309 11884372003076880310639183)
          ·
            refine ⟨17826558004615320465958775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11884372003076880310639183 17826558004615320465958775)
            ·
              refine ⟨26739837006922980698938163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17826558004615320465958775 26739837006922980698938163)
              ·
                refine ⟨40109755510384471048407245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26739837006922980698938163 40109755510384471048407245)
                ·
                  refine ⟨15041158316394176643152717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40109755510384471048407245 15041158316394176643152717)
                  ·
                    refine ⟨5640434368647816241182269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15041158316394176643152717 5640434368647816241182269)
                    ·
                      refine ⟨2115162888242931090443351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5640434368647816241182269 2115162888242931090443351)
                      ·
                        rfl

theorem cell23_4119265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 1, 1, 3, 3, 3].length) (baseStart_4119265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4119265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4119265 prefixEnd_4119265 := by exact prefixLift 4119265
  have htrace : WordTrace (prefixWord ++ tailWord_4119265) baseStart_4119265 baseEnd_4119265 := by
    simpa [prefixWord, tailWord_4119265, baseEnd_4119265] using wordTrace_append hprefix tailTrace_4119265
  have hstable : (prefixWord ++ tailWord_4119265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4119265).length < 2 ^ (prefixWord ++ tailWord_4119265).sum := by decide
  have hdescent : baseEnd_4119265 < baseStart_4119265 := by decide
  rcases family_descends (prefixWord ++ tailWord_4119265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4119269 : List Nat := [1, 3, 1, 4, 1, 3, 3, 1, 1, 2, 3]
def baseStart_4119269 : Nat := 118140960795 + 4119269 * 2 ^ 59
def prefixEnd_4119269 : Nat := 4983230072969 + 3 ^ 40 * 4119269 * 2
def baseEnd_4119269 : Nat := 2115164942165549074793333

theorem tailTrace_4119269 : CollatzResearch.WordTrace tailWord_4119269 prefixEnd_4119269 2115164942165549074793333 := by
  unfold tailWord_4119269
  simp only [CollatzResearch.WordTrace]
  refine ⟨150242083313599402980608861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100161388875732935320405907 150242083313599402980608861)
  ·
    refine ⟨56340781242599776117728323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 150242083313599402980608861 56340781242599776117728323)
    ·
      refine ⟨84511171863899664176592485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56340781242599776117728323 84511171863899664176592485)
      ·
        refine ⟨15845844724481187033111091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 84511171863899664176592485 15845844724481187033111091)
        ·
          refine ⟨23768767086721780549666637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15845844724481187033111091 23768767086721780549666637)
          ·
            refine ⟨8913287657520667706124989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23768767086721780549666637 8913287657520667706124989)
            ·
              refine ⟨3342482871570250389796871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8913287657520667706124989 3342482871570250389796871)
              ·
                refine ⟨5013724307355375584695307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3342482871570250389796871 5013724307355375584695307)
                ·
                  refine ⟨7520586461033063377042961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5013724307355375584695307 7520586461033063377042961)
                  ·
                    refine ⟨5640439845774797532782221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7520586461033063377042961 5640439845774797532782221)
                    ·
                      refine ⟨2115164942165549074793333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5640439845774797532782221 2115164942165549074793333)
                      ·
                        rfl

theorem cell23_4119269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 3, 1, 1, 2, 3].length) (baseStart_4119269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4119269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4119269 prefixEnd_4119269 := by exact prefixLift 4119269
  have htrace : WordTrace (prefixWord ++ tailWord_4119269) baseStart_4119269 baseEnd_4119269 := by
    simpa [prefixWord, tailWord_4119269, baseEnd_4119269] using wordTrace_append hprefix tailTrace_4119269
  have hstable : (prefixWord ++ tailWord_4119269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4119269).length < 2 ^ (prefixWord ++ tailWord_4119269).sum := by decide
  have hdescent : baseEnd_4119269 < baseStart_4119269 := by decide
  rcases family_descends (prefixWord ++ tailWord_4119269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4119288 : List Nat := [2, 1, 2, 1, 1, 2, 3, 1, 1, 5, 4]
def baseStart_4119288 : Nat := 118140960795 + 4119288 * 2 ^ 59
def prefixEnd_4119288 : Nat := 4983230072969 + 3 ^ 40 * 4119288 * 2
def baseEnd_4119288 : Nat := 2115174698297984500455745

theorem tailTrace_4119288 : CollatzResearch.WordTrace tailWord_4119288 prefixEnd_4119288 2115174698297984500455745 := by
  unfold tailWord_4119288
  simp only [CollatzResearch.WordTrace]
  refine ⟨75121388150265284612775259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100161850867020379483700345 75121388150265284612775259)
  ·
    refine ⟨112682082225397926919162889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75121388150265284612775259 112682082225397926919162889)
    ·
      refine ⟨84511561669048445189372167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112682082225397926919162889 84511561669048445189372167)
      ·
        refine ⟨126767342503572667784058251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84511561669048445189372167 126767342503572667784058251)
        ·
          refine ⟨190151013755359001676087377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126767342503572667784058251 190151013755359001676087377)
          ·
            refine ⟨142613260316519251257065533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 190151013755359001676087377 142613260316519251257065533)
            ·
              refine ⟨53479972618694719221399575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 142613260316519251257065533 53479972618694719221399575)
              ·
                refine ⟨80219958928042078832099363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53479972618694719221399575 80219958928042078832099363)
                ·
                  refine ⟨120329938392063118248149045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 80219958928042078832099363 120329938392063118248149045)
                  ·
                    refine ⟨11280931724255917335763973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 120329938392063118248149045 11280931724255917335763973)
                    ·
                      refine ⟨2115174698297984500455745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11280931724255917335763973 2115174698297984500455745)
                      ·
                        rfl

theorem cell23_4119288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 1, 1, 5, 4].length) (baseStart_4119288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4119288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4119288 prefixEnd_4119288 := by exact prefixLift 4119288
  have htrace : WordTrace (prefixWord ++ tailWord_4119288) baseStart_4119288 baseEnd_4119288 := by
    simpa [prefixWord, tailWord_4119288, baseEnd_4119288] using wordTrace_append hprefix tailTrace_4119288
  have hstable : (prefixWord ++ tailWord_4119288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4119288).length < 2 ^ (prefixWord ++ tailWord_4119288).sum := by decide
  have hdescent : baseEnd_4119288 < baseStart_4119288 := by decide
  rcases family_descends (prefixWord ++ tailWord_4119288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4119292 : List Nat := [2, 2, 2, 1, 3, 2, 1, 2, 3, 3, 2]
def baseStart_4119292 : Nat := 118140960795 + 4119292 * 2 ^ 59
def prefixEnd_4119292 : Nat := 4983230072969 + 3 ^ 40 * 4119292 * 2
def baseEnd_4119292 : Nat := 2115176752220602484805727

theorem tailTrace_4119292 : CollatzResearch.WordTrace tailWord_4119292 prefixEnd_4119292 2115176752220602484805727 := by
  unfold tailWord_4119292
  simp only [CollatzResearch.WordTrace]
  refine ⟨75121461096258038954348065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100161948128344051939130753 75121461096258038954348065)
  ·
    refine ⟨56341095822193529215761049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75121461096258038954348065 56341095822193529215761049)
    ·
      refine ⟨42255821866645146911820787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56341095822193529215761049 42255821866645146911820787)
      ·
        refine ⟨63383732799967720367731181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42255821866645146911820787 63383732799967720367731181)
        ·
          refine ⟨23768899799987895137899193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63383732799967720367731181 23768899799987895137899193)
          ·
            refine ⟨17826674849990921353424395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23768899799987895137899193 17826674849990921353424395)
            ·
              refine ⟨26740012274986382030136593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17826674849990921353424395 26740012274986382030136593)
              ·
                refine ⟨20055009206239786522602445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26740012274986382030136593 20055009206239786522602445)
                ·
                  refine ⟨7520628452339919945975917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20055009206239786522602445 7520628452339919945975917)
                  ·
                    refine ⟨2820235669627469979740969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7520628452339919945975917 2820235669627469979740969)
                    ·
                      refine ⟨2115176752220602484805727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2820235669627469979740969 2115176752220602484805727)
                      ·
                        rfl

theorem cell23_4119292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 1, 2, 3, 3, 2].length) (baseStart_4119292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4119292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4119292 prefixEnd_4119292 := by exact prefixLift 4119292
  have htrace : WordTrace (prefixWord ++ tailWord_4119292) baseStart_4119292 baseEnd_4119292 := by
    simpa [prefixWord, tailWord_4119292, baseEnd_4119292] using wordTrace_append hprefix tailTrace_4119292
  have hstable : (prefixWord ++ tailWord_4119292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4119292).length < 2 ^ (prefixWord ++ tailWord_4119292).sum := by decide
  have hdescent : baseEnd_4119292 < baseStart_4119292 := by decide
  rcases family_descends (prefixWord ++ tailWord_4119292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4119322 : List Nat := [3, 1, 1, 3, 2, 1, 1, 4, 1, 4, 2]
def baseStart_4119322 : Nat := 118140960795 + 4119322 * 2 ^ 59
def prefixEnd_4119322 : Nat := 4983230072969 + 3 ^ 40 * 4119322 * 2
def baseEnd_4119322 : Nat := 2115192156640237367430589

theorem tailTrace_4119322 : CollatzResearch.WordTrace tailWord_4119322 prefixEnd_4119322 2115192156640237367430589 := by
  unfold tailWord_4119322
  simp only [CollatzResearch.WordTrace]
  refine ⟨37561004095601848258072055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100162677588271595354858813 37561004095601848258072055)
  ·
    refine ⟨56341506143402772387108083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37561004095601848258072055 56341506143402772387108083)
    ·
      refine ⟨84512259215104158580662125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56341506143402772387108083 84512259215104158580662125)
      ·
        refine ⟨31692097205664059467748297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84512259215104158580662125 31692097205664059467748297)
        ·
          refine ⟨23769072904248044600811223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31692097205664059467748297 23769072904248044600811223)
          ·
            refine ⟨35653609356372066901216835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23769072904248044600811223 35653609356372066901216835)
            ·
              refine ⟨53480414034558100351825253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35653609356372066901216835 53480414034558100351825253)
              ·
                refine ⟨10027577631479643815967235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53480414034558100351825253 10027577631479643815967235)
                ·
                  refine ⟨15041366447219465723950853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10027577631479643815967235 15041366447219465723950853)
                  ·
                    refine ⟨2820256208853649823240785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15041366447219465723950853 2820256208853649823240785)
                    ·
                      refine ⟨2115192156640237367430589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2820256208853649823240785 2115192156640237367430589)
                      ·
                        rfl

theorem cell23_4119322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 4, 1, 4, 2].length) (baseStart_4119322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4119322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4119322 prefixEnd_4119322 := by exact prefixLift 4119322
  have htrace : WordTrace (prefixWord ++ tailWord_4119322) baseStart_4119322 baseEnd_4119322 := by
    simpa [prefixWord, tailWord_4119322, baseEnd_4119322] using wordTrace_append hprefix tailTrace_4119322
  have hstable : (prefixWord ++ tailWord_4119322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4119322).length < 2 ^ (prefixWord ++ tailWord_4119322).sum := by decide
  have hdescent : baseEnd_4119322 < baseStart_4119322 := by decide
  rcases family_descends (prefixWord ++ tailWord_4119322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4119345 : List Nat := [1, 2, 2, 3, 2, 1, 4, 1, 7]
def baseStart_4119345 : Nat := 118140960795 + 4119345 * 2 ^ 59
def prefixEnd_4119345 : Nat := 4983230072969 + 3 ^ 40 * 4119345 * 2
def baseEnd_4119345 : Nat := 235022662966143419715887

theorem tailTrace_4119345 : CollatzResearch.WordTrace tailWord_4119345 prefixEnd_4119345 235022662966143419715887 := by
  unfold tailWord_4119345
  simp only [CollatzResearch.WordTrace]
  refine ⟨150244855261324067960375489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100163236840882711973583659 150244855261324067960375489)
  ·
    refine ⟨112683641445993050970281617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150244855261324067960375489 112683641445993050970281617)
    ·
      refine ⟨84512731084494788227711213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112683641445993050970281617 84512731084494788227711213)
      ·
        refine ⟨31692274156685545585391705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84512731084494788227711213 31692274156685545585391705)
        ·
          refine ⟨23769205617514159189043779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31692274156685545585391705 23769205617514159189043779)
          ·
            refine ⟨35653808426271238783565669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23769205617514159189043779 35653808426271238783565669)
            ·
              refine ⟨6685089079925857271918563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35653808426271238783565669 6685089079925857271918563)
              ·
                refine ⟨10027633619888785907877845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6685089079925857271918563 10027633619888785907877845)
                ·
                  refine ⟨235022662966143419715887, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10027633619888785907877845 235022662966143419715887)
                  ·
                    rfl

theorem cell23_4119345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 4, 1, 7].length) (baseStart_4119345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4119345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4119345 prefixEnd_4119345 := by exact prefixLift 4119345
  have htrace : WordTrace (prefixWord ++ tailWord_4119345) baseStart_4119345 baseEnd_4119345 := by
    simpa [prefixWord, tailWord_4119345, baseEnd_4119345] using wordTrace_append hprefix tailTrace_4119345
  have hstable : (prefixWord ++ tailWord_4119345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4119345).length < 2 ^ (prefixWord ++ tailWord_4119345).sum := by decide
  have hdescent : baseEnd_4119345 < baseStart_4119345 := by decide
  rcases family_descends (prefixWord ++ tailWord_4119345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4119415 : List Nat := [1, 1, 3, 1, 1, 2, 1, 3, 3, 4, 3]
def baseStart_4119415 : Nat := 118140960795 + 4119415 * 2 ^ 59
def prefixEnd_4119415 : Nat := 4983230072969 + 3 ^ 40 * 4119415 * 2
def baseEnd_4119415 : Nat := 2115239910341105503567661

theorem tailTrace_4119415 : CollatzResearch.WordTrace tailWord_4119415 prefixEnd_4119415 2115239910341105503567661 := by
  unfold tailWord_4119415
  simp only [CollatzResearch.WordTrace]
  refine ⟨150247408371070469915423699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100164938914046979943615799 150247408371070469915423699)
  ·
    refine ⟨225371112556605704873135549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150247408371070469915423699 225371112556605704873135549)
    ·
      refine ⟨84514167208727139327425831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 225371112556605704873135549 84514167208727139327425831)
      ·
        refine ⟨126771250813090708991138747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84514167208727139327425831 126771250813090708991138747)
        ·
          refine ⟨190156876219636063486708121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126771250813090708991138747 190156876219636063486708121)
          ·
            refine ⟨142617657164727047615031091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 190156876219636063486708121 142617657164727047615031091)
            ·
              refine ⟨213926485747090571422546637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 142617657164727047615031091 213926485747090571422546637)
              ·
                refine ⟨80222432155158964283454989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 213926485747090571422546637 80222432155158964283454989)
                ·
                  refine ⟨30083412058184611606295621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 80222432155158964283454989 30083412058184611606295621)
                  ·
                    refine ⟨5640639760909614676180429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30083412058184611606295621 5640639760909614676180429)
                    ·
                      refine ⟨2115239910341105503567661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5640639760909614676180429 2115239910341105503567661)
                      ·
                        rfl

theorem cell23_4119415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 3, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 3, 3, 4, 3].length) (baseStart_4119415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4119415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4119415 prefixEnd_4119415 := by exact prefixLift 4119415
  have htrace : WordTrace (prefixWord ++ tailWord_4119415) baseStart_4119415 baseEnd_4119415 := by
    simpa [prefixWord, tailWord_4119415, baseEnd_4119415] using wordTrace_append hprefix tailTrace_4119415
  have hstable : (prefixWord ++ tailWord_4119415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4119415).length < 2 ^ (prefixWord ++ tailWord_4119415).sum := by decide
  have hdescent : baseEnd_4119415 < baseStart_4119415 := by decide
  rcases family_descends (prefixWord ++ tailWord_4119415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4119456 : List Nat := [2, 1, 1, 4, 1, 1, 6, 2, 1, 4]
def baseStart_4119456 : Nat := 118140960795 + 4119456 * 2 ^ 59
def prefixEnd_4119456 : Nat := 4983230072969 + 3 ^ 40 * 4119456 * 2
def baseEnd_4119456 : Nat := 705086987682646614384991

theorem tailTrace_4119456 : CollatzResearch.WordTrace tailWord_4119456 prefixEnd_4119456 705086987682646614384991 := by
  unfold tailWord_4119456
  simp only [CollatzResearch.WordTrace]
  refine ⟨75124451881960966958833111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100165935842614622611777481 75124451881960966958833111)
  ·
    refine ⟨112686677822941450438249667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75124451881960966958833111 112686677822941450438249667)
    ·
      refine ⟨169030016734412175657374501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112686677822941450438249667 169030016734412175657374501)
      ·
        refine ⟨31693128137702282935757719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 169030016734412175657374501 31693128137702282935757719)
        ·
          refine ⟨47539692206553424403636579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31693128137702282935757719 47539692206553424403636579)
          ·
            refine ⟨71309538309830136605454869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47539692206553424403636579 71309538309830136605454869)
            ·
              refine ⟨3342634608273287653380697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 71309538309830136605454869 3342634608273287653380697)
              ·
                refine ⟨2506975956204965740035523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3342634608273287653380697 2506975956204965740035523)
                ·
                  refine ⟨3760463934307448610053285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2506975956204965740035523 3760463934307448610053285)
                  ·
                    refine ⟨705086987682646614384991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3760463934307448610053285 705086987682646614384991)
                    ·
                      rfl

theorem cell23_4119456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 6, 2, 1, 4].length) (baseStart_4119456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4119456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4119456 prefixEnd_4119456 := by exact prefixLift 4119456
  have htrace : WordTrace (prefixWord ++ tailWord_4119456) baseStart_4119456 baseEnd_4119456 := by
    simpa [prefixWord, tailWord_4119456, baseEnd_4119456] using wordTrace_append hprefix tailTrace_4119456
  have hstable : (prefixWord ++ tailWord_4119456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4119456).length < 2 ^ (prefixWord ++ tailWord_4119456).sum := by decide
  have hdescent : baseEnd_4119456 < baseStart_4119456 := by decide
  rcases family_descends (prefixWord ++ tailWord_4119456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4119465 : List Nat := [1, 2, 1, 1, 1, 1, 5, 1, 5, 5]
def baseStart_4119465 : Nat := 118140960795 + 4119465 * 2 ^ 59
def prefixEnd_4119465 : Nat := 4983230072969 + 3 ^ 40 * 4119465 * 2
def baseEnd_4119465 : Nat := 705088528124610102647477

theorem tailTrace_4119465 : CollatzResearch.WordTrace tailWord_4119465 prefixEnd_4119465 705088528124610102647477 := by
  unfold tailWord_4119465
  simp only [CollatzResearch.WordTrace]
  refine ⟨150249232020889328454743849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100166154680592885636495899 150249232020889328454743849)
  ·
    refine ⟨112686924015666996341057887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150249232020889328454743849 112686924015666996341057887)
    ·
      refine ⟨169030386023500494511586831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112686924015666996341057887 169030386023500494511586831)
      ·
        refine ⟨253545579035250741767380247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169030386023500494511586831 253545579035250741767380247)
        ·
          refine ⟨380318368552876112651070371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 253545579035250741767380247 380318368552876112651070371)
          ·
            refine ⟨570477552829314168976605557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 380318368552876112651070371 570477552829314168976605557)
            ·
              refine ⟨53482270577748203341556771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 570477552829314168976605557 53482270577748203341556771)
              ·
                refine ⟨80223405866622305012335157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53482270577748203341556771 80223405866622305012335157)
                ·
                  refine ⟨7520944299995841094906421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 80223405866622305012335157 7520944299995841094906421)
                  ·
                    refine ⟨705088528124610102647477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7520944299995841094906421 705088528124610102647477)
                    ·
                      rfl

theorem cell23_4119465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 1, 5, 5].length) (baseStart_4119465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4119465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4119465 prefixEnd_4119465 := by exact prefixLift 4119465
  have htrace : WordTrace (prefixWord ++ tailWord_4119465) baseStart_4119465 baseEnd_4119465 := by
    simpa [prefixWord, tailWord_4119465, baseEnd_4119465] using wordTrace_append hprefix tailTrace_4119465
  have hstable : (prefixWord ++ tailWord_4119465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4119465).length < 2 ^ (prefixWord ++ tailWord_4119465).sum := by decide
  have hdescent : baseEnd_4119465 < baseStart_4119465 := by decide
  rcases family_descends (prefixWord ++ tailWord_4119465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4119482 : List Nat := [3, 1, 1, 1, 2, 1, 4, 4, 1, 5]
def baseStart_4119482 : Nat := 118140960795 + 4119482 * 2 ^ 59
def prefixEnd_4119482 : Nat := 4983230072969 + 3 ^ 40 * 4119482 * 2
def baseEnd_4119482 : Nat := 705091437848318913809951

theorem tailTrace_4119482 : CollatzResearch.WordTrace tailWord_4119482 prefixEnd_4119482 705091437848318913809951 := by
  unfold tailWord_4119482
  simp only [CollatzResearch.WordTrace]
  refine ⟨37562463015456935089528175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100166568041218493572075133 37562463015456935089528175)
  ·
    refine ⟨56343694523185402634292263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37562463015456935089528175 56343694523185402634292263)
    ·
      refine ⟨84515541784778103951438395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56343694523185402634292263 84515541784778103951438395)
      ·
        refine ⟨126773312677167155927157593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84515541784778103951438395 126773312677167155927157593)
        ·
          refine ⟨95079984507875366945368195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126773312677167155927157593 95079984507875366945368195)
          ·
            refine ⟨142619976761813050418052293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95079984507875366945368195 142619976761813050418052293)
            ·
              refine ⟨26741245642839946953384805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 142619976761813050418052293 26741245642839946953384805)
              ·
                refine ⟨5013983558032490053759651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26741245642839946953384805 5013983558032490053759651)
                ·
                  refine ⟨7520975337048735080639477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5013983558032490053759651 7520975337048735080639477)
                  ·
                    refine ⟨705091437848318913809951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7520975337048735080639477 705091437848318913809951)
                    ·
                      rfl

theorem cell23_4119482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 4, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 4, 4, 1, 5].length) (baseStart_4119482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4119482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4119482 prefixEnd_4119482 := by exact prefixLift 4119482
  have htrace : WordTrace (prefixWord ++ tailWord_4119482) baseStart_4119482 baseEnd_4119482 := by
    simpa [prefixWord, tailWord_4119482, baseEnd_4119482] using wordTrace_append hprefix tailTrace_4119482
  have hstable : (prefixWord ++ tailWord_4119482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4119482).length < 2 ^ (prefixWord ++ tailWord_4119482).sum := by decide
  have hdescent : baseEnd_4119482 < baseStart_4119482 := by decide
  rcases family_descends (prefixWord ++ tailWord_4119482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4119499 : List Nat := [1, 1, 1, 1, 3, 5, 4, 1, 1, 5]
def baseStart_4119499 : Nat := 118140960795 + 4119499 * 2 ^ 59
def prefixEnd_4119499 : Nat := 4983230072969 + 3 ^ 40 * 4119499 * 2
def baseEnd_4119499 : Nat := 705094347572027724972425

theorem tailTrace_4119499 : CollatzResearch.WordTrace tailWord_4119499 prefixEnd_4119499 705094347572027724972425 := by
  unfold tailWord_4119499
  simp only [CollatzResearch.WordTrace]
  refine ⟨150250472102766152261481551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100166981401844101507654367 150250472102766152261481551)
  ·
    refine ⟨225375708154149228392222327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150250472102766152261481551 225375708154149228392222327)
    ·
      refine ⟨338063562231223842588333491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225375708154149228392222327 338063562231223842588333491)
      ·
        refine ⟨507095343346835763882500237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 338063562231223842588333491 507095343346835763882500237)
        ·
          refine ⟨190160753755063411455937589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 507095343346835763882500237 190160753755063411455937589)
          ·
            refine ⟨17827570664537194823994149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 190160753755063411455937589 17827570664537194823994149)
            ·
              refine ⟨3342669499600724029498903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17827570664537194823994149 3342669499600724029498903)
              ·
                refine ⟨5014004249401086044248355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3342669499600724029498903 5014004249401086044248355)
                ·
                  refine ⟨7521006374101629066372533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5014004249401086044248355 7521006374101629066372533)
                  ·
                    refine ⟨705094347572027724972425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7521006374101629066372533 705094347572027724972425)
                    ·
                      rfl

theorem cell23_4119499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 4, 1, 1, 5].length) (baseStart_4119499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4119499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4119499 prefixEnd_4119499 := by exact prefixLift 4119499
  have htrace : WordTrace (prefixWord ++ tailWord_4119499) baseStart_4119499 baseEnd_4119499 := by
    simpa [prefixWord, tailWord_4119499, baseEnd_4119499] using wordTrace_append hprefix tailTrace_4119499
  have hstable : (prefixWord ++ tailWord_4119499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4119499).length < 2 ^ (prefixWord ++ tailWord_4119499).sum := by decide
  have hdescent : baseEnd_4119499 < baseStart_4119499 := by decide
  rcases family_descends (prefixWord ++ tailWord_4119499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4119555 : List Nat := [1, 1, 1, 3, 2, 1, 1, 1, 3, 9]
def baseStart_4119555 : Nat := 118140960795 + 4119555 * 2 ^ 59
def prefixEnd_4119555 : Nat := 4983230072969 + 3 ^ 40 * 4119555 * 2
def baseEnd_4119555 : Nat := 705103932544244985272339

theorem tailTrace_4119555 : CollatzResearch.WordTrace tailWord_4119555 prefixEnd_4119555 705103932544244985272339 := by
  unfold tailWord_4119555
  simp only [CollatzResearch.WordTrace]
  refine ⟨150252514590563273825520119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100168343060375515883680079 150252514590563273825520119)
  ·
    refine ⟨225378771885844910738280179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150252514590563273825520119 225378771885844910738280179)
    ·
      refine ⟨338068157828767366107420269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225378771885844910738280179 338068157828767366107420269)
      ·
        refine ⟨126775559185787762290282601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 338068157828767366107420269 126775559185787762290282601)
        ·
          refine ⟨95081669389340821717711951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126775559185787762290282601 95081669389340821717711951)
          ·
            refine ⟨142622504084011232576567927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95081669389340821717711951 142622504084011232576567927)
            ·
              refine ⟨213933756126016848864851891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 142622504084011232576567927 213933756126016848864851891)
              ·
                refine ⟨320900634189025273297277837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 213933756126016848864851891 320900634189025273297277837)
                ·
                  refine ⟨120337737820884477486479189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 320900634189025273297277837 120337737820884477486479189)
                  ·
                    refine ⟨705103932544244985272339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 120337737820884477486479189 705103932544244985272339)
                    ·
                      rfl

theorem cell23_4119555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 1, 3, 9].length) (baseStart_4119555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4119555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4119555 prefixEnd_4119555 := by exact prefixLift 4119555
  have htrace : WordTrace (prefixWord ++ tailWord_4119555) baseStart_4119555 baseEnd_4119555 := by
    simpa [prefixWord, tailWord_4119555, baseEnd_4119555] using wordTrace_append hprefix tailTrace_4119555
  have hstable : (prefixWord ++ tailWord_4119555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4119555).length < 2 ^ (prefixWord ++ tailWord_4119555).sum := by decide
  have hdescent : baseEnd_4119555 < baseStart_4119555 := by decide
  rcases family_descends (prefixWord ++ tailWord_4119555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4119580 : List Nat := [2, 2, 3, 1, 5, 1, 2, 1, 2, 4]
def baseStart_4119580 : Nat := 118140960795 + 4119580 * 2 ^ 59
def prefixEnd_4119580 : Nat := 4983230072969 + 3 ^ 40 * 4119580 * 2
def baseEnd_4119580 : Nat := 705108211549699119334801

theorem tailTrace_4119580 : CollatzResearch.WordTrace tailWord_4119580 prefixEnd_4119580 705108211549699119334801 := by
  unfold tailWord_4119580
  simp only [CollatzResearch.WordTrace]
  refine ⟨75126713207736351547590097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100168950943648468730120129 75126713207736351547590097)
  ·
    refine ⟨56345034905802263660692573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75126713207736351547590097 56345034905802263660692573)
    ·
      refine ⟨21129388089675848872759715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56345034905802263660692573 21129388089675848872759715)
      ·
        refine ⟨31694082134513773309139573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21129388089675848872759715 31694082134513773309139573)
        ·
          refine ⟨2971320200110666247731835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 31694082134513773309139573 2971320200110666247731835)
          ·
            refine ⟨4456980300165999371597753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2971320200110666247731835 4456980300165999371597753)
            ·
              refine ⟨3342735225124499528698315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4456980300165999371597753 3342735225124499528698315)
              ·
                refine ⟨5014102837686749293047473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3342735225124499528698315 5014102837686749293047473)
                ·
                  refine ⟨3760577128265061969785605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5014102837686749293047473 3760577128265061969785605)
                  ·
                    refine ⟨705108211549699119334801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3760577128265061969785605 705108211549699119334801)
                    ·
                      rfl

theorem cell23_4119580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 5, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 5, 1, 2, 1, 2, 4].length) (baseStart_4119580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4119580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4119580 prefixEnd_4119580 := by exact prefixLift 4119580
  have htrace : WordTrace (prefixWord ++ tailWord_4119580) baseStart_4119580 baseEnd_4119580 := by
    simpa [prefixWord, tailWord_4119580, baseEnd_4119580] using wordTrace_append hprefix tailTrace_4119580
  have hstable : (prefixWord ++ tailWord_4119580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4119580).length < 2 ^ (prefixWord ++ tailWord_4119580).sum := by decide
  have hdescent : baseEnd_4119580 < baseStart_4119580 := by decide
  rcases family_descends (prefixWord ++ tailWord_4119580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4119626 : List Nat := [3, 1, 2, 1, 1, 2, 2, 3, 4, 2, 2]
def baseStart_4119626 : Nat := 118140960795 + 4119626 * 2 ^ 59
def prefixEnd_4119626 : Nat := 4983230072969 + 3 ^ 40 * 4119626 * 2
def baseEnd_4119626 : Nat := 2115348254759204178029191

theorem tailTrace_4119626 : CollatzResearch.WordTrace tailWord_4119626 prefixEnd_4119626 2115348254759204178029191 := by
  unfold tailWord_4119626
  simp only [CollatzResearch.WordTrace]
  refine ⟨37563776043326513237838683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100170069448870701967569821 37563776043326513237838683)
  ·
    refine ⟨56345664064989769856758025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37563776043326513237838683 56345664064989769856758025)
    ·
      refine ⟨42259248048742327392568519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56345664064989769856758025 42259248048742327392568519)
      ·
        refine ⟨63388872073113491088852779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42259248048742327392568519 63388872073113491088852779)
        ·
          refine ⟨95083308109670236633279169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63388872073113491088852779 95083308109670236633279169)
          ·
            refine ⟨71312481082252677474959377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95083308109670236633279169 71312481082252677474959377)
            ·
              refine ⟨53484360811689508106219533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71312481082252677474959377 53484360811689508106219533)
              ·
                refine ⟨20056635304383565539832325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53484360811689508106219533 20056635304383565539832325)
                ·
                  refine ⟨3760619119571918538718561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20056635304383565539832325 3760619119571918538718561)
                  ·
                    refine ⟨2820464339678938904038921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3760619119571918538718561 2820464339678938904038921)
                    ·
                      refine ⟨2115348254759204178029191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2820464339678938904038921 2115348254759204178029191)
                      ·
                        rfl

theorem cell23_4119626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 3, 4, 2, 2].length) (baseStart_4119626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4119626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4119626 prefixEnd_4119626 := by exact prefixLift 4119626
  have htrace : WordTrace (prefixWord ++ tailWord_4119626) baseStart_4119626 baseEnd_4119626 := by
    simpa [prefixWord, tailWord_4119626, baseEnd_4119626] using wordTrace_append hprefix tailTrace_4119626
  have hstable : (prefixWord ++ tailWord_4119626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4119626).length < 2 ^ (prefixWord ++ tailWord_4119626).sum := by decide
  have hdescent : baseEnd_4119626 < baseStart_4119626 := by decide
  rcases family_descends (prefixWord ++ tailWord_4119626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4119666 : List Nat := [3, 2, 1, 2, 2, 1, 4, 3, 5]
def baseStart_4119666 : Nat := 118140960795 + 4119666 * 2 ^ 59
def prefixEnd_4119666 : Nat := 4983230072969 + 3 ^ 40 * 4119666 * 2
def baseEnd_4119666 : Nat := 235040977109487113503223

theorem tailTrace_4119666 : CollatzResearch.WordTrace tailWord_4119666 prefixEnd_4119666 235040977109487113503223 := by
  unfold tailWord_4119666
  simp only [CollatzResearch.WordTrace]
  refine ⟨37564140773290284945702713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100171042062107426521873901 37564140773290284945702713)
  ·
    refine ⟨28173105579967713709277035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37564140773290284945702713 28173105579967713709277035)
    ·
      refine ⟨42259658369951570563915553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28173105579967713709277035 42259658369951570563915553)
      ·
        refine ⟨31694743777463677922936665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42259658369951570563915553 31694743777463677922936665)
        ·
          refine ⟨23771057833097758442202499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31694743777463677922936665 23771057833097758442202499)
          ·
            refine ⟨35656586749646637663303749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23771057833097758442202499 35656586749646637663303749)
            ·
              refine ⟨6685610015558744561869453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35656586749646637663303749 6685610015558744561869453)
              ·
                refine ⟨2507103755834529210701045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6685610015558744561869453 2507103755834529210701045)
                ·
                  refine ⟨235040977109487113503223, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2507103755834529210701045 235040977109487113503223)
                  ·
                    rfl

theorem cell23_4119666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 4, 3, 5].length) (baseStart_4119666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4119666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4119666 prefixEnd_4119666 := by exact prefixLift 4119666
  have htrace : WordTrace (prefixWord ++ tailWord_4119666) baseStart_4119666 baseEnd_4119666 := by
    simpa [prefixWord, tailWord_4119666, baseEnd_4119666] using wordTrace_append hprefix tailTrace_4119666
  have hstable : (prefixWord ++ tailWord_4119666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4119666).length < 2 ^ (prefixWord ++ tailWord_4119666).sum := by decide
  have hdescent : baseEnd_4119666 < baseStart_4119666 := by decide
  rcases family_descends (prefixWord ++ tailWord_4119666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4119672 : List Nat := [2, 1, 2, 1, 1, 1, 4, 1, 3, 2, 5]
def baseStart_4119672 : Nat := 118140960795 + 4119672 * 2 ^ 59
def prefixEnd_4119672 : Nat := 4983230072969 + 3 ^ 40 * 4119672 * 2
def baseEnd_4119672 : Nat := 2115371874869310998053979

theorem tailTrace_4119672 : CollatzResearch.WordTrace tailWord_4119672 prefixEnd_4119672 2115371874869310998053979 := by
  unfold tailWord_4119672
  simp only [CollatzResearch.WordTrace]
  refine ⟨75128390965569701403764635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100171187954092935205019513 75128390965569701403764635)
  ·
    refine ⟨112692586448354552105646953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75128390965569701403764635 112692586448354552105646953)
    ·
      refine ⟨84519439836265914079235215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112692586448354552105646953 84519439836265914079235215)
      ·
        refine ⟨126779159754398871118852823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84519439836265914079235215 126779159754398871118852823)
        ·
          refine ⟨190168739631598306678279235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126779159754398871118852823 190168739631598306678279235)
          ·
            refine ⟨285253109447397460017418853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 190168739631598306678279235 285253109447397460017418853)
            ·
              refine ⟨53484958021387023753266035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 285253109447397460017418853 53484958021387023753266035)
              ·
                refine ⟨80227437032080535629899053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53484958021387023753266035 80227437032080535629899053)
                ·
                  refine ⟨30085288887030200861212145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 80227437032080535629899053 30085288887030200861212145)
                  ·
                    refine ⟨22563966665272650645909109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30085288887030200861212145 22563966665272650645909109)
                    ·
                      refine ⟨2115371874869310998053979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22563966665272650645909109 2115371874869310998053979)
                      ·
                        rfl

theorem cell23_4119672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 1, 3, 2, 5].length) (baseStart_4119672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4119672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4119672 prefixEnd_4119672 := by exact prefixLift 4119672
  have htrace : WordTrace (prefixWord ++ tailWord_4119672) baseStart_4119672 baseEnd_4119672 := by
    simpa [prefixWord, tailWord_4119672, baseEnd_4119672] using wordTrace_append hprefix tailTrace_4119672
  have hstable : (prefixWord ++ tailWord_4119672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4119672).length < 2 ^ (prefixWord ++ tailWord_4119672).sum := by decide
  have hdescent : baseEnd_4119672 < baseStart_4119672 := by decide
  rcases family_descends (prefixWord ++ tailWord_4119672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4119794 : List Nat := [3, 2, 1, 3, 4, 1, 2, 2, 1, 4]
def baseStart_4119794 : Nat := 118140960795 + 4119794 * 2 ^ 59
def prefixEnd_4119794 : Nat := 4983230072969 + 3 ^ 40 * 4119794 * 2
def baseEnd_4119794 : Nat := 705144839836386506909473

theorem tailTrace_4119794 : CollatzResearch.WordTrace tailWord_4119794 prefixEnd_4119794 705144839836386506909473 := by
  unfold tailWord_4119794
  simp only [CollatzResearch.WordTrace]
  refine ⟨37565307909174354410867609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100174154424464945095646957 37565307909174354410867609)
  ·
    refine ⟨28173980931880765808150707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37565307909174354410867609 28173980931880765808150707)
    ·
      refine ⟨42260971397821148712226061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28173980931880765808150707 42260971397821148712226061)
      ·
        refine ⟨15847864274182930767084773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42260971397821148712226061 15847864274182930767084773)
        ·
          refine ⟨2971474551409299518828395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15847864274182930767084773 2971474551409299518828395)
          ·
            refine ⟨4457211827113949278242593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2971474551409299518828395 4457211827113949278242593)
            ·
              refine ⟨3342908870335461958681945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4457211827113949278242593 3342908870335461958681945)
              ·
                refine ⟨2507181652751596469011459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3342908870335461958681945 2507181652751596469011459)
                ·
                  refine ⟨3760772479127394703517189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2507181652751596469011459 3760772479127394703517189)
                  ·
                    refine ⟨705144839836386506909473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3760772479127394703517189 705144839836386506909473)
                    ·
                      rfl

theorem cell23_4119794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 4, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 4, 1, 2, 2, 1, 4].length) (baseStart_4119794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4119794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4119794 prefixEnd_4119794 := by exact prefixLift 4119794
  have htrace : WordTrace (prefixWord ++ tailWord_4119794) baseStart_4119794 baseEnd_4119794 := by
    simpa [prefixWord, tailWord_4119794, baseEnd_4119794] using wordTrace_append hprefix tailTrace_4119794
  have hstable : (prefixWord ++ tailWord_4119794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4119794).length < 2 ^ (prefixWord ++ tailWord_4119794).sum := by decide
  have hdescent : baseEnd_4119794 < baseStart_4119794 := by decide
  rcases family_descends (prefixWord ++ tailWord_4119794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4119836 : List Nat := [2, 2, 3, 1, 1, 1, 4, 2, 1, 2, 4]
def baseStart_4119836 : Nat := 118140960795 + 4119836 * 2 ^ 59
def prefixEnd_4119836 : Nat := 4983230072969 + 3 ^ 40 * 4119836 * 2
def baseEnd_4119836 : Nat := 2115456085696648356403225

theorem tailTrace_4119836 : CollatzResearch.WordTrace tailWord_4119836 prefixEnd_4119836 2115456085696648356403225 := by
  unfold tailWord_4119836
  simp only [CollatzResearch.WordTrace]
  refine ⟨75131381751272629408249681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100175175668363505877666241 75131381751272629408249681)
  ·
    refine ⟨56348536313454472056187261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75131381751272629408249681 56348536313454472056187261)
    ·
      refine ⟨21130701117545427021070223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56348536313454472056187261 21130701117545427021070223)
      ·
        refine ⟨31696051676318140531605335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21130701117545427021070223 31696051676318140531605335)
        ·
          refine ⟨47544077514477210797408003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31696051676318140531605335 47544077514477210797408003)
          ·
            refine ⟨71316116271715816196112005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47544077514477210797408003 71316116271715816196112005)
            ·
              refine ⟨13371771800946715536771001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 71316116271715816196112005 13371771800946715536771001)
              ·
                refine ⟨10028828850710036652578251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13371771800946715536771001 10028828850710036652578251)
                ·
                  refine ⟨15043243276065054978867377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10028828850710036652578251 15043243276065054978867377)
                  ·
                    refine ⟨11282432457048791234150533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15043243276065054978867377 11282432457048791234150533)
                    ·
                      refine ⟨2115456085696648356403225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11282432457048791234150533 2115456085696648356403225)
                      ·
                        rfl

theorem cell23_4119836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 4, 2, 1, 2, 4].length) (baseStart_4119836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4119836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4119836 prefixEnd_4119836 := by exact prefixLift 4119836
  have htrace : WordTrace (prefixWord ++ tailWord_4119836) baseStart_4119836 baseEnd_4119836 := by
    simpa [prefixWord, tailWord_4119836, baseEnd_4119836] using wordTrace_append hprefix tailTrace_4119836
  have hstable : (prefixWord ++ tailWord_4119836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4119836).length < 2 ^ (prefixWord ++ tailWord_4119836).sum := by decide
  have hdescent : baseEnd_4119836 < baseStart_4119836 := by decide
  rcases family_descends (prefixWord ++ tailWord_4119836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4119843 : List Nat := [1, 1, 1, 4, 2, 4, 1, 3, 1, 2, 3]
def baseStart_4119843 : Nat := 118140960795 + 4119843 * 2 ^ 59
def prefixEnd_4119843 : Nat := 4983230072969 + 3 ^ 40 * 4119843 * 2
def baseEnd_4119843 : Nat := 2115459680061229829015693

theorem tailTrace_4119843 : CollatzResearch.WordTrace tailWord_4119843 prefixEnd_4119843 2115459680061229829015693 := by
  unfold tailWord_4119843
  simp only [CollatzResearch.WordTrace]
  refine ⟨150263018813519899012004183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100175345875679932674669455 150263018813519899012004183)
  ·
    refine ⟨225394528220279848518006275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150263018813519899012004183 225394528220279848518006275)
    ·
      refine ⟨338091792330419772777009413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225394528220279848518006275 338091792330419772777009413)
      ·
        refine ⟨63392211061953707395689265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 338091792330419772777009413 63392211061953707395689265)
        ·
          refine ⟨47544158296465280546766949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63392211061953707395689265 47544158296465280546766949)
          ·
            refine ⟨8914529680587240102518803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47544158296465280546766949 8914529680587240102518803)
            ·
              refine ⟨13371794520880860153778205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8914529680587240102518803 13371794520880860153778205)
              ·
                refine ⟨5014422945330322557666827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13371794520880860153778205 5014422945330322557666827)
                ·
                  refine ⟨7521634417995483836500241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5014422945330322557666827 7521634417995483836500241)
                  ·
                    refine ⟨5641225813496612877375181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7521634417995483836500241 5641225813496612877375181)
                    ·
                      refine ⟨2115459680061229829015693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5641225813496612877375181 2115459680061229829015693)
                      ·
                        rfl

theorem cell23_4119843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 1, 3, 1, 2, 3].length) (baseStart_4119843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4119843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4119843 prefixEnd_4119843 := by exact prefixLift 4119843
  have htrace : WordTrace (prefixWord ++ tailWord_4119843) baseStart_4119843 baseEnd_4119843 := by
    simpa [prefixWord, tailWord_4119843, baseEnd_4119843] using wordTrace_append hprefix tailTrace_4119843
  have hstable : (prefixWord ++ tailWord_4119843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4119843).length < 2 ^ (prefixWord ++ tailWord_4119843).sum := by decide
  have hdescent : baseEnd_4119843 < baseStart_4119843 := by decide
  rcases family_descends (prefixWord ++ tailWord_4119843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4119850 : List Nat := [3, 1, 4, 2, 1, 1, 3, 2, 2, 4]
def baseStart_4119850 : Nat := 118140960795 + 4119850 * 2 ^ 59
def prefixEnd_4119850 : Nat := 4983230072969 + 3 ^ 40 * 4119850 * 2
def baseEnd_4119850 : Nat := 705154424808603767209387

theorem tailTrace_4119850 : CollatzResearch.WordTrace tailWord_4119850 prefixEnd_4119850 705154424808603767209387 := by
  unfold tailWord_4119850
  simp only [CollatzResearch.WordTrace]
  refine ⟨37565818531123634801877251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100175516082996359471672669 37565818531123634801877251)
  ·
    refine ⟨56348727796685452202815877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37565818531123634801877251 56348727796685452202815877)
    ·
      refine ⟨10565386461878522288027977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 56348727796685452202815877 10565386461878522288027977)
      ·
        refine ⟨7924039846408891716020983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10565386461878522288027977 7924039846408891716020983)
        ·
          refine ⟨11886059769613337574031475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7924039846408891716020983 11886059769613337574031475)
          ·
            refine ⟨17829089654420006361047213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11886059769613337574031475 17829089654420006361047213)
            ·
              refine ⟨6685908620407502385392705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17829089654420006361047213 6685908620407502385392705)
              ·
                refine ⟨5014431465305626789044529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6685908620407502385392705 5014431465305626789044529)
                ·
                  refine ⟨3760823598979220091783397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5014431465305626789044529 3760823598979220091783397)
                  ·
                    refine ⟨705154424808603767209387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3760823598979220091783397 705154424808603767209387)
                    ·
                      rfl

theorem cell23_4119850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 3, 2, 2, 4].length) (baseStart_4119850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4119850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4119850 prefixEnd_4119850 := by exact prefixLift 4119850
  have htrace : WordTrace (prefixWord ++ tailWord_4119850) baseStart_4119850 baseEnd_4119850 := by
    simpa [prefixWord, tailWord_4119850, baseEnd_4119850] using wordTrace_append hprefix tailTrace_4119850
  have hstable : (prefixWord ++ tailWord_4119850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4119850).length < 2 ^ (prefixWord ++ tailWord_4119850).sum := by decide
  have hdescent : baseEnd_4119850 < baseStart_4119850 := by decide
  rcases family_descends (prefixWord ++ tailWord_4119850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4119857 : List Nat := [1, 2, 2, 3, 3, 1, 2, 4, 1, 2, 2]
def baseStart_4119857 : Nat := 118140960795 + 4119857 * 2 ^ 59
def prefixEnd_4119857 : Nat := 4983230072969 + 3 ^ 40 * 4119857 * 2
def baseEnd_4119857 : Nat := 2115466868790392774240629

theorem tailTrace_4119857 : CollatzResearch.WordTrace tailWord_4119857 prefixEnd_4119857 2115466868790392774240629 := by
  unfold tailWord_4119857
  simp only [CollatzResearch.WordTrace]
  refine ⟨150263529435469179403013825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100175686290312786268675883 150263529435469179403013825)
  ·
    refine ⟨112697647076601884552260369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150263529435469179403013825 112697647076601884552260369)
    ·
      refine ⟨84523235307451413414195277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112697647076601884552260369 84523235307451413414195277)
      ·
        refine ⟨31696213240294280030323229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84523235307451413414195277 31696213240294280030323229)
        ·
          refine ⟨11886079965110355011371211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31696213240294280030323229 11886079965110355011371211)
          ·
            refine ⟨17829119947665532517056817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11886079965110355011371211 17829119947665532517056817)
            ·
              refine ⟨13371839960749149387792613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17829119947665532517056817 13371839960749149387792613)
              ·
                refine ⟨2507219992640465510211115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13371839960749149387792613 2507219992640465510211115)
                ·
                  refine ⟨3760829988960698265316673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2507219992640465510211115 3760829988960698265316673)
                  ·
                    refine ⟨2820622491720523698987505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3760829988960698265316673 2820622491720523698987505)
                    ·
                      refine ⟨2115466868790392774240629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2820622491720523698987505 2115466868790392774240629)
                      ·
                        rfl

theorem cell23_4119857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 2, 4, 1, 2, 2].length) (baseStart_4119857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4119857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4119857 prefixEnd_4119857 := by exact prefixLift 4119857
  have htrace : WordTrace (prefixWord ++ tailWord_4119857) baseStart_4119857 baseEnd_4119857 := by
    simpa [prefixWord, tailWord_4119857, baseEnd_4119857] using wordTrace_append hprefix tailTrace_4119857
  have hstable : (prefixWord ++ tailWord_4119857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4119857).length < 2 ^ (prefixWord ++ tailWord_4119857).sum := by decide
  have hdescent : baseEnd_4119857 < baseStart_4119857 := by decide
  rcases family_descends (prefixWord ++ tailWord_4119857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4119894 : List Nat := [5, 2, 3, 1, 1, 1, 2, 1, 1, 1, 5]
def baseStart_4119894 : Nat := 118140960795 + 4119894 * 2 ^ 59
def prefixEnd_4119894 : Nat := 4983230072969 + 3 ^ 40 * 4119894 * 2
def baseEnd_4119894 : Nat := 2115485867574609129477959

theorem tailTrace_4119894 : CollatzResearch.WordTrace tailWord_4119894 prefixEnd_4119894 2115485867574609129477959 := by
  unfold tailWord_4119894
  simp only [CollatzResearch.WordTrace]
  refine ⟨9391554933520945920131921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 100176585957556756481407157 9391554933520945920131921)
  ·
    refine ⟨7043666200140709440098941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9391554933520945920131921 7043666200140709440098941)
    ·
      refine ⟨2641374825052766040037103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7043666200140709440098941 2641374825052766040037103)
      ·
        refine ⟨3962062237579149060055655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2641374825052766040037103 3962062237579149060055655)
        ·
          refine ⟨5943093356368723590083483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3962062237579149060055655 5943093356368723590083483)
          ·
            refine ⟨8914640034553085385125225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5943093356368723590083483 8914640034553085385125225)
            ·
              refine ⟨6685980025914814038843919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8914640034553085385125225 6685980025914814038843919)
              ·
                refine ⟨10028970038872221058265879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6685980025914814038843919 10028970038872221058265879)
                ·
                  refine ⟨15043455058308331587398819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10028970038872221058265879 15043455058308331587398819)
                  ·
                    refine ⟨22565182587462497381098229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15043455058308331587398819 22565182587462497381098229)
                    ·
                      refine ⟨2115485867574609129477959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22565182587462497381098229 2115485867574609129477959)
                      ·
                        rfl

theorem cell23_4119894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 2, 1, 1, 1, 5].length) (baseStart_4119894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4119894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4119894 prefixEnd_4119894 := by exact prefixLift 4119894
  have htrace : WordTrace (prefixWord ++ tailWord_4119894) baseStart_4119894 baseEnd_4119894 := by
    simpa [prefixWord, tailWord_4119894, baseEnd_4119894] using wordTrace_append hprefix tailTrace_4119894
  have hstable : (prefixWord ++ tailWord_4119894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4119894).length < 2 ^ (prefixWord ++ tailWord_4119894).sum := by decide
  have hdescent : baseEnd_4119894 < baseStart_4119894 := by decide
  rcases family_descends (prefixWord ++ tailWord_4119894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4119930 : List Nat := [3, 1, 1, 1, 1, 1, 2, 7, 2, 2, 2]
def baseStart_4119930 : Nat := 118140960795 + 4119930 * 2 ^ 59
def prefixEnd_4119930 : Nat := 4983230072969 + 3 ^ 40 * 4119930 * 2
def baseEnd_4119930 : Nat := 2115504352878170988627793

theorem tailTrace_4119930 : CollatzResearch.WordTrace tailWord_4119930 prefixEnd_4119930 2115504352878170988627793 := by
  unfold tailWord_4119930
  simp only [CollatzResearch.WordTrace]
  refine ⟨37566547991051178217605311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100177461309469808580280829 37566547991051178217605311)
  ·
    refine ⟨56349821986576767326407967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37566547991051178217605311 56349821986576767326407967)
    ·
      refine ⟨84524732979865150989611951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56349821986576767326407967 84524732979865150989611951)
      ·
        refine ⟨126787099469797726484417927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84524732979865150989611951 126787099469797726484417927)
        ·
          refine ⟨190180649204696589726626891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126787099469797726484417927 190180649204696589726626891)
          ·
            refine ⟨285270973807044884589940337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 190180649204696589726626891 285270973807044884589940337)
            ·
              refine ⟨213953230355283663442455253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 285270973807044884589940337 213953230355283663442455253)
              ·
                refine ⟨5014528836451960861932545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 213953230355283663442455253 5014528836451960861932545)
                ·
                  refine ⟨3760896627338970646449409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5014528836451960861932545 3760896627338970646449409)
                  ·
                    refine ⟨2820672470504227984837057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3760896627338970646449409 2820672470504227984837057)
                    ·
                      refine ⟨2115504352878170988627793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2820672470504227984837057 2115504352878170988627793)
                      ·
                        rfl

theorem cell23_4119930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 7, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 7, 2, 2, 2].length) (baseStart_4119930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4119930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4119930 prefixEnd_4119930 := by exact prefixLift 4119930
  have htrace : WordTrace (prefixWord ++ tailWord_4119930) baseStart_4119930 baseEnd_4119930 := by
    simpa [prefixWord, tailWord_4119930, baseEnd_4119930] using wordTrace_append hprefix tailTrace_4119930
  have hstable : (prefixWord ++ tailWord_4119930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4119930).length < 2 ^ (prefixWord ++ tailWord_4119930).sum := by decide
  have hdescent : baseEnd_4119930 < baseStart_4119930 := by decide
  rcases family_descends (prefixWord ++ tailWord_4119930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4119934 : List Nat := [4, 2, 3, 2, 1, 1, 1, 1, 3, 3, 2]
def baseStart_4119934 : Nat := 118140960795 + 4119934 * 2 ^ 59
def prefixEnd_4119934 : Nat := 4983230072969 + 3 ^ 40 * 4119934 * 2
def baseEnd_4119934 : Nat := 2115506406800788972977775

theorem tailTrace_4119934 : CollatzResearch.WordTrace tailWord_4119934 prefixEnd_4119934 2115506406800788972977775 := by
  unfold tailWord_4119934
  simp only [CollatzResearch.WordTrace]
  refine ⟨18783292232023777694195857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 100177558570793481035711237 18783292232023777694195857)
  ·
    refine ⟨14087469174017833270646893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18783292232023777694195857 14087469174017833270646893)
    ·
      refine ⟨5282800940256687476492585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14087469174017833270646893 5282800940256687476492585)
      ·
        refine ⟨3962100705192515607369439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5282800940256687476492585 3962100705192515607369439)
        ·
          refine ⟨5943151057788773411054159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3962100705192515607369439 5943151057788773411054159)
          ·
            refine ⟨8914726586683160116581239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5943151057788773411054159 8914726586683160116581239)
            ·
              refine ⟨13372089880024740174871859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8914726586683160116581239 13372089880024740174871859)
              ·
                refine ⟨20058134820037110262307789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13372089880024740174871859 20058134820037110262307789)
                ·
                  refine ⟨7521800557513916348365421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20058134820037110262307789 7521800557513916348365421)
                  ·
                    refine ⟨2820675209067718630637033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7521800557513916348365421 2820675209067718630637033)
                    ·
                      refine ⟨2115506406800788972977775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2820675209067718630637033 2115506406800788972977775)
                      ·
                        rfl

theorem cell23_4119934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 1, 1, 3, 3, 2].length) (baseStart_4119934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4119934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4119934 prefixEnd_4119934 := by exact prefixLift 4119934
  have htrace : WordTrace (prefixWord ++ tailWord_4119934) baseStart_4119934 baseEnd_4119934 := by
    simpa [prefixWord, tailWord_4119934, baseEnd_4119934] using wordTrace_append hprefix tailTrace_4119934
  have hstable : (prefixWord ++ tailWord_4119934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4119934).length < 2 ^ (prefixWord ++ tailWord_4119934).sum := by decide
  have hdescent : baseEnd_4119934 < baseStart_4119934 := by decide
  rcases family_descends (prefixWord ++ tailWord_4119934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4119970 : List Nat := [3, 3, 1, 2, 1, 3, 1, 4, 5]
def baseStart_4119970 : Nat := 118140960795 + 4119970 * 2 ^ 59
def prefixEnd_4119970 : Nat := 4983230072969 + 3 ^ 40 * 4119970 * 2
def baseEnd_4119970 : Nat := 235058321344927870236401

theorem tailTrace_4119970 : CollatzResearch.WordTrace tailWord_4119970 prefixEnd_4119970 235058321344927870236401 := by
  unfold tailWord_4119970
  simp only [CollatzResearch.WordTrace]
  refine ⟨37566912721014949925469341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100178433922706533134584909 37566912721014949925469341)
  ·
    refine ⟨14087592270380606222051003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37566912721014949925469341 14087592270380606222051003)
    ·
      refine ⟨21131388405570909333076505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14087592270380606222051003 21131388405570909333076505)
      ·
        refine ⟨15848541304178181999807379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21131388405570909333076505 15848541304178181999807379)
        ·
          refine ⟨23772811956267272999711069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15848541304178181999807379 23772811956267272999711069)
          ·
            refine ⟨8914804483600227374891651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23772811956267272999711069 8914804483600227374891651)
            ·
              refine ⟨13372206725400341062337477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8914804483600227374891651 13372206725400341062337477)
              ·
                refine ⟨2507288761012563949188277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13372206725400341062337477 2507288761012563949188277)
                ·
                  refine ⟨235058321344927870236401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2507288761012563949188277 235058321344927870236401)
                  ·
                    rfl

theorem cell23_4119970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 1, 4, 5].length) (baseStart_4119970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4119970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4119970 prefixEnd_4119970 := by exact prefixLift 4119970
  have htrace : WordTrace (prefixWord ++ tailWord_4119970) baseStart_4119970 baseEnd_4119970 := by
    simpa [prefixWord, tailWord_4119970, baseEnd_4119970] using wordTrace_append hprefix tailTrace_4119970
  have hstable : (prefixWord ++ tailWord_4119970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4119970).length < 2 ^ (prefixWord ++ tailWord_4119970).sum := by decide
  have hdescent : baseEnd_4119970 < baseStart_4119970 := by decide
  rcases family_descends (prefixWord ++ tailWord_4119970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4120002 : List Nat := [3, 5, 2, 1, 2, 1, 2, 1, 1, 3, 2]
def baseStart_4120002 : Nat := 118140960795 + 4120002 * 2 ^ 59
def prefixEnd_4120002 : Nat := 4983230072969 + 3 ^ 40 * 4120002 * 2
def baseEnd_4120002 : Nat := 2115541323485294706927463

theorem tailTrace_4120002 : CollatzResearch.WordTrace tailWord_4120002 prefixEnd_4120002 2115541323485294706927463 := by
  unfold tailWord_4120002
  simp only [CollatzResearch.WordTrace]
  refine ⟨37567204504985967291760565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100179212013295912778028173 37567204504985967291760565)
  ·
    refine ⟨3521925422342434433602553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 37567204504985967291760565 3521925422342434433602553)
    ·
      refine ⟨2641444066756825825201915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3521925422342434433602553 2641444066756825825201915)
      ·
        refine ⟨3962166100135238737802873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2641444066756825825201915 3962166100135238737802873)
        ·
          refine ⟨2971624575101429053352155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3962166100135238737802873 2971624575101429053352155)
          ·
            refine ⟨4457436862652143580028233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2971624575101429053352155 4457436862652143580028233)
            ·
              refine ⟨3343077646989107685021175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4457436862652143580028233 3343077646989107685021175)
              ·
                refine ⟨5014616470483661527531763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3343077646989107685021175 5014616470483661527531763)
                ·
                  refine ⟨7521924705725492291297645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5014616470483661527531763 7521924705725492291297645)
                  ·
                    refine ⟨2820721764647059609236617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7521924705725492291297645 2820721764647059609236617)
                    ·
                      refine ⟨2115541323485294706927463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2820721764647059609236617 2115541323485294706927463)
                      ·
                        rfl

theorem cell23_4120002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 2, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 2, 1, 2, 1, 1, 3, 2].length) (baseStart_4120002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4120002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4120002 prefixEnd_4120002 := by exact prefixLift 4120002
  have htrace : WordTrace (prefixWord ++ tailWord_4120002) baseStart_4120002 baseEnd_4120002 := by
    simpa [prefixWord, tailWord_4120002, baseEnd_4120002] using wordTrace_append hprefix tailTrace_4120002
  have hstable : (prefixWord ++ tailWord_4120002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4120002).length < 2 ^ (prefixWord ++ tailWord_4120002).sum := by decide
  have hdescent : baseEnd_4120002 < baseStart_4120002 := by decide
  rcases family_descends (prefixWord ++ tailWord_4120002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4120003 : List Nat := [1, 1, 1, 3, 1, 1, 7, 1, 2, 1, 4]
def baseStart_4120003 : Nat := 118140960795 + 4120003 * 2 ^ 59
def prefixEnd_4120003 : Nat := 4983230072969 + 3 ^ 40 * 4120003 * 2
def baseEnd_4120003 : Nat := 2115541836965949203014957

theorem tailTrace_4120003 : CollatzResearch.WordTrace tailWord_4120003 prefixEnd_4120003 2115541836965949203014957 := by
  unfold tailWord_4120003
  simp only [CollatzResearch.WordTrace]
  refine ⟨150268854492940246337828663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100179236328626830891885775 150268854492940246337828663)
  ·
    refine ⟨225403281739410369506742995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150268854492940246337828663 225403281739410369506742995)
    ·
      refine ⟨338104922609115554260114493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225403281739410369506742995 338104922609115554260114493)
      ·
        refine ⟨126789345978418332847542935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 338104922609115554260114493 126789345978418332847542935)
        ·
          refine ⟨190184018967627499271314403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126789345978418332847542935 190184018967627499271314403)
          ·
            refine ⟨285276028451441248906971605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 190184018967627499271314403 285276028451441248906971605)
            ·
              refine ⟨6686156916830654271257147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 285276028451441248906971605 6686156916830654271257147)
              ·
                refine ⟨10029235375245981406885721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6686156916830654271257147 10029235375245981406885721)
                ·
                  refine ⟨7521926531434486055164291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10029235375245981406885721 7521926531434486055164291)
                  ·
                    refine ⟨11282889797151729082746437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7521926531434486055164291 11282889797151729082746437)
                    ·
                      refine ⟨2115541836965949203014957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11282889797151729082746437 2115541836965949203014957)
                      ·
                        rfl

theorem cell23_4120003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 7, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 7, 1, 2, 1, 4].length) (baseStart_4120003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4120003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4120003 prefixEnd_4120003 := by exact prefixLift 4120003
  have htrace : WordTrace (prefixWord ++ tailWord_4120003) baseStart_4120003 baseEnd_4120003 := by
    simpa [prefixWord, tailWord_4120003, baseEnd_4120003] using wordTrace_append hprefix tailTrace_4120003
  have hstable : (prefixWord ++ tailWord_4120003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4120003).length < 2 ^ (prefixWord ++ tailWord_4120003).sum := by decide
  have hdescent : baseEnd_4120003 < baseStart_4120003 := by decide
  rcases family_descends (prefixWord ++ tailWord_4120003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4120023 : List Nat := [1, 1, 3, 2, 1, 1, 1, 6, 2, 2, 3]
def baseStart_4120023 : Nat := 118140960795 + 4120023 * 2 ^ 59
def prefixEnd_4120023 : Nat := 4983230072969 + 3 ^ 40 * 4120023 * 2
def baseEnd_4120023 : Nat := 2115552106579039124764865

theorem tailTrace_4120023 : CollatzResearch.WordTrace tailWord_4120023 prefixEnd_4120023 2115552106579039124764865 := by
  unfold tailWord_4120023
  simp only [CollatzResearch.WordTrace]
  refine ⟨150269583952867789753556723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100179722635245193169037815 150269583952867789753556723)
  ·
    refine ⟨225404375929301684630335085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150269583952867789753556723 225404375929301684630335085)
    ·
      refine ⟨84526640973488131736375657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 225404375929301684630335085 84526640973488131736375657)
      ·
        refine ⟨63394980730116098802281743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84526640973488131736375657 63394980730116098802281743)
        ·
          refine ⟨95092471095174148203422615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63394980730116098802281743 95092471095174148203422615)
          ·
            refine ⟨142638706642761222305133923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95092471095174148203422615 142638706642761222305133923)
            ·
              refine ⟨213958059964141833457700885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 142638706642761222305133923 213958059964141833457700885)
              ·
                refine ⟨10029284060819148443329729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 213958059964141833457700885 10029284060819148443329729)
                ·
                  refine ⟨7521963045614361332497297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10029284060819148443329729 7521963045614361332497297)
                  ·
                    refine ⟨5641472284210770999372973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7521963045614361332497297 5641472284210770999372973)
                    ·
                      refine ⟨2115552106579039124764865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5641472284210770999372973 2115552106579039124764865)
                      ·
                        rfl

theorem cell23_4120023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 6, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 6, 2, 2, 3].length) (baseStart_4120023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4120023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4120023 prefixEnd_4120023 := by exact prefixLift 4120023
  have htrace : WordTrace (prefixWord ++ tailWord_4120023) baseStart_4120023 baseEnd_4120023 := by
    simpa [prefixWord, tailWord_4120023, baseEnd_4120023] using wordTrace_append hprefix tailTrace_4120023
  have hstable : (prefixWord ++ tailWord_4120023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4120023).length < 2 ^ (prefixWord ++ tailWord_4120023).sum := by decide
  have hdescent : baseEnd_4120023 < baseStart_4120023 := by decide
  rcases family_descends (prefixWord ++ tailWord_4120023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4120073 : List Nat := [1, 2, 1, 1, 3, 1, 3, 5, 1, 5]
def baseStart_4120073 : Nat := 118140960795 + 4120073 * 2 ^ 59
def prefixEnd_4120073 : Nat := 4983230072969 + 3 ^ 40 * 4120073 * 2
def baseEnd_4120073 : Nat := 705192593537254643046545

theorem tailTrace_4120073 : CollatzResearch.WordTrace tailWord_4120073 prefixEnd_4120073 705192593537254643046545 := by
  unfold tailWord_4120073
  simp only [CollatzResearch.WordTrace]
  refine ⟨150271407602686648292876873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100180938401791098861917915 150271407602686648292876873)
  ·
    refine ⟨112703555702014986219657655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150271407602686648292876873 112703555702014986219657655)
    ·
      refine ⟨169055333553022479329486483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112703555702014986219657655 169055333553022479329486483)
      ·
        refine ⟨253583000329533718994229725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169055333553022479329486483 253583000329533718994229725)
        ·
          refine ⟨95093625123575144622836147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 253583000329533718994229725 95093625123575144622836147)
          ·
            refine ⟨142640437685362716934254221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95093625123575144622836147 142640437685362716934254221)
            ·
              refine ⟨53490164132011018850345333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 142640437685362716934254221 53490164132011018850345333)
              ·
                refine ⟨5014702887376033017219875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 53490164132011018850345333 5014702887376033017219875)
                ·
                  refine ⟨7522054331064049525829813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5014702887376033017219875 7522054331064049525829813)
                  ·
                    refine ⟨705192593537254643046545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7522054331064049525829813 705192593537254643046545)
                    ·
                      rfl

theorem cell23_4120073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 5, 1, 5].length) (baseStart_4120073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4120073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4120073 prefixEnd_4120073 := by exact prefixLift 4120073
  have htrace : WordTrace (prefixWord ++ tailWord_4120073) baseStart_4120073 baseEnd_4120073 := by
    simpa [prefixWord, tailWord_4120073, baseEnd_4120073] using wordTrace_append hprefix tailTrace_4120073
  have hstable : (prefixWord ++ tailWord_4120073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4120073).length < 2 ^ (prefixWord ++ tailWord_4120073).sum := by decide
  have hdescent : baseEnd_4120073 < baseStart_4120073 := by decide
  rcases family_descends (prefixWord ++ tailWord_4120073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4120127 : List Nat := [1, 1, 2, 2, 3, 4, 3, 1, 1, 1, 4]
def baseStart_4120127 : Nat := 118140960795 + 4120127 * 2 ^ 59
def prefixEnd_4120127 : Nat := 4983230072969 + 3 ^ 40 * 4120127 * 2
def baseEnd_4120127 : Nat := 2115605508567106717864387

theorem tailTrace_4120127 : CollatzResearch.WordTrace tailWord_4120127 prefixEnd_4120127 2115605508567106717864387 := by
  unfold tailWord_4120127
  simp only [CollatzResearch.WordTrace]
  refine ⟨150273377144491015515342635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100182251429660677010228423 150273377144491015515342635)
  ·
    refine ⟨225410065716736523273013953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150273377144491015515342635 225410065716736523273013953)
    ·
      refine ⟨169057549287552392454760465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 225410065716736523273013953 169057549287552392454760465)
      ·
        refine ⟨126793161965664294341070349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 169057549287552392454760465 126793161965664294341070349)
        ·
          refine ⟨47547435737124110377901381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 126793161965664294341070349 47547435737124110377901381)
          ·
            refine ⟨8915144200710770695856509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47547435737124110377901381 8915144200710770695856509)
            ·
              refine ⟨3343179075266539010946191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8915144200710770695856509 3343179075266539010946191)
              ·
                refine ⟨5014768612899808516419287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3343179075266539010946191 5014768612899808516419287)
                ·
                  refine ⟨7522152919349712774628931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5014768612899808516419287 7522152919349712774628931)
                  ·
                    refine ⟨11283229379024569161943397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7522152919349712774628931 11283229379024569161943397)
                    ·
                      refine ⟨2115605508567106717864387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11283229379024569161943397 2115605508567106717864387)
                      ·
                        rfl

theorem cell23_4120127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 3, 1, 1, 1, 4].length) (baseStart_4120127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4120127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4120127 prefixEnd_4120127 := by exact prefixLift 4120127
  have htrace : WordTrace (prefixWord ++ tailWord_4120127) baseStart_4120127 baseEnd_4120127 := by
    simpa [prefixWord, tailWord_4120127, baseEnd_4120127] using wordTrace_append hprefix tailTrace_4120127
  have hstable : (prefixWord ++ tailWord_4120127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4120127).length < 2 ^ (prefixWord ++ tailWord_4120127).sum := by decide
  have hdescent : baseEnd_4120127 < baseStart_4120127 := by decide
  rcases family_descends (prefixWord ++ tailWord_4120127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4120143 : List Nat := [1, 1, 2, 1, 1, 2, 3, 1, 5, 3, 3]
def baseStart_4120143 : Nat := 118140960795 + 4120143 * 2 ^ 59
def prefixEnd_4120143 : Nat := 4983230072969 + 3 ^ 40 * 4120143 * 2
def baseEnd_4120143 : Nat := 2115613724257578655264313

theorem tailTrace_4120143 : CollatzResearch.WordTrace tailWord_4120143 prefixEnd_4120143 2115613724257578655264313 := by
  unfold tailWord_4120143
  simp only [CollatzResearch.WordTrace]
  refine ⟨150273960712433050247925083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100182640474955366831950055 150273960712433050247925083)
  ·
    refine ⟨225410941068649575371887625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150273960712433050247925083 225410941068649575371887625)
    ·
      refine ⟨169058205801487181528915719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 225410941068649575371887625 169058205801487181528915719)
      ·
        refine ⟨253587308702230772293373579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169058205801487181528915719 253587308702230772293373579)
        ·
          refine ⟨380380963053346158440060369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 253587308702230772293373579 380380963053346158440060369)
          ·
            refine ⟨285285722290009618830045277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 380380963053346158440060369 285285722290009618830045277)
            ·
              refine ⟨106982145858753607061266979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 285285722290009618830045277 106982145858753607061266979)
              ·
                refine ⟨160473218788130410591900469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 106982145858753607061266979 160473218788130410591900469)
                ·
                  refine ⟨15044364261387225992990669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 160473218788130410591900469 15044364261387225992990669)
                  ·
                    refine ⟨5641636598020209747371501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15044364261387225992990669 5641636598020209747371501)
                    ·
                      refine ⟨2115613724257578655264313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5641636598020209747371501 2115613724257578655264313)
                      ·
                        rfl

theorem cell23_4120143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 1, 5, 3, 3].length) (baseStart_4120143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4120143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4120143 prefixEnd_4120143 := by exact prefixLift 4120143
  have htrace : WordTrace (prefixWord ++ tailWord_4120143) baseStart_4120143 baseEnd_4120143 := by
    simpa [prefixWord, tailWord_4120143, baseEnd_4120143] using wordTrace_append hprefix tailTrace_4120143
  have hstable : (prefixWord ++ tailWord_4120143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4120143).length < 2 ^ (prefixWord ++ tailWord_4120143).sum := by decide
  have hdescent : baseEnd_4120143 < baseStart_4120143 := by decide
  rcases family_descends (prefixWord ++ tailWord_4120143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4120144 : List Nat := [2, 1, 1, 1, 1, 3, 5, 4, 1, 2, 2]
def baseStart_4120144 : Nat := 118140960795 + 4120144 * 2 ^ 59
def prefixEnd_4120144 : Nat := 4983230072969 + 3 ^ 40 * 4120144 * 2
def baseEnd_4120144 : Nat := 2115614237738233151351809

theorem tailTrace_4120144 : CollatzResearch.WordTrace tailWord_4120144 prefixEnd_4120144 2115614237738233151351809 := by
  unfold tailWord_4120144
  simp only [CollatzResearch.WordTrace]
  refine ⟨75136998592714713709355743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100182664790286284945807657 75136998592714713709355743)
  ·
    refine ⟨112705497889072070564033615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75136998592714713709355743 112705497889072070564033615)
    ·
      refine ⟨169058246833608105846050423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112705497889072070564033615 169058246833608105846050423)
      ·
        refine ⟨253587370250412158769075635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169058246833608105846050423 253587370250412158769075635)
        ·
          refine ⟨380381055375618238153613453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 253587370250412158769075635 380381055375618238153613453)
          ·
            refine ⟨142642895765856839307605045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 380381055375618238153613453 142642895765856839307605045)
            ·
              refine ⟨13372771478049078685087973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 142642895765856839307605045 13372771478049078685087973)
              ·
                refine ⟨2507394652134202253453995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13372771478049078685087973 2507394652134202253453995)
                ·
                  refine ⟨3761091978201303380180993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2507394652134202253453995 3761091978201303380180993)
                  ·
                    refine ⟨2820818983650977535135745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3761091978201303380180993 2820818983650977535135745)
                    ·
                      refine ⟨2115614237738233151351809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2820818983650977535135745 2115614237738233151351809)
                      ·
                        rfl

theorem cell23_4120144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 5, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 5, 4, 1, 2, 2].length) (baseStart_4120144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4120144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4120144 prefixEnd_4120144 := by exact prefixLift 4120144
  have htrace : WordTrace (prefixWord ++ tailWord_4120144) baseStart_4120144 baseEnd_4120144 := by
    simpa [prefixWord, tailWord_4120144, baseEnd_4120144] using wordTrace_append hprefix tailTrace_4120144
  have hstable : (prefixWord ++ tailWord_4120144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4120144).length < 2 ^ (prefixWord ++ tailWord_4120144).sum := by decide
  have hdescent : baseEnd_4120144 < baseStart_4120144 := by decide
  rcases family_descends (prefixWord ++ tailWord_4120144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4120160 : List Nat := [2, 1, 1, 3, 2, 1, 1, 2, 6, 1, 3]
def baseStart_4120160 : Nat := 118140960795 + 4120160 * 2 ^ 59
def prefixEnd_4120160 : Nat := 4983230072969 + 3 ^ 40 * 4120160 * 2
def baseEnd_4120160 : Nat := 2115622453428705088751735

theorem tailTrace_4120160 : CollatzResearch.WordTrace tailWord_4120160 prefixEnd_4120160 2115622453428705088751735 := by
  unfold tailWord_4120160
  simp only [CollatzResearch.WordTrace]
  refine ⟨75137290376685731075646967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100183053835580974767529289 75137290376685731075646967)
  ·
    refine ⟨112705935565028596613470451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75137290376685731075646967 112705935565028596613470451)
    ·
      refine ⟨169058903347542894920205677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112705935565028596613470451 169058903347542894920205677)
      ·
        refine ⟨63397088755328585595077129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 169058903347542894920205677 63397088755328585595077129)
        ·
          refine ⟨47547816566496439196307847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63397088755328585595077129 47547816566496439196307847)
          ·
            refine ⟨71321724849744658794461771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47547816566496439196307847 71321724849744658794461771)
            ·
              refine ⟨106982587274616988191692657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71321724849744658794461771 106982587274616988191692657)
              ·
                refine ⟨80236940455962741143769493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 106982587274616988191692657 80236940455962741143769493)
                ·
                  refine ⟨3761106583873253491114195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 80236940455962741143769493 3761106583873253491114195)
                  ·
                    refine ⟨5641659875809880236671293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3761106583873253491114195 5641659875809880236671293)
                    ·
                      refine ⟨2115622453428705088751735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5641659875809880236671293 2115622453428705088751735)
                      ·
                        rfl

theorem cell23_4120160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 2, 6, 1, 3].length) (baseStart_4120160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4120160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4120160 prefixEnd_4120160 := by exact prefixLift 4120160
  have htrace : WordTrace (prefixWord ++ tailWord_4120160) baseStart_4120160 baseEnd_4120160 := by
    simpa [prefixWord, tailWord_4120160, baseEnd_4120160] using wordTrace_append hprefix tailTrace_4120160
  have hstable : (prefixWord ++ tailWord_4120160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4120160).length < 2 ^ (prefixWord ++ tailWord_4120160).sum := by decide
  have hdescent : baseEnd_4120160 < baseStart_4120160 := by decide
  rcases family_descends (prefixWord ++ tailWord_4120160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4120181 : List Nat := [1, 3, 4, 2, 1, 3, 2, 1, 1, 2, 3]
def baseStart_4120181 : Nat := 118140960795 + 4120181 * 2 ^ 59
def prefixEnd_4120181 : Nat := 4983230072969 + 3 ^ 40 * 4120181 * 2
def baseEnd_4120181 : Nat := 2115633236522449506589139

theorem tailTrace_4120181 : CollatzResearch.WordTrace tailWord_4120181 prefixEnd_4120181 2115633236522449506589139 := by
  unfold tailWord_4120181
  simp only [CollatzResearch.WordTrace]
  refine ⟨150275346686295382737808397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100183564457530255158538931 150275346686295382737808397)
  ·
    refine ⟨56353255007360768526678149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 150275346686295382737808397 56353255007360768526678149)
    ·
      refine ⟨10566235313880144098752153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 56353255007360768526678149 10566235313880144098752153)
      ·
        refine ⟨7924676485410108074064115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10566235313880144098752153 7924676485410108074064115)
        ·
          refine ⟨11887014728115162111096173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7924676485410108074064115 11887014728115162111096173)
          ·
            refine ⟨4457630523043185791661065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11887014728115162111096173 4457630523043185791661065)
            ·
              refine ⟨3343222892282389343745799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4457630523043185791661065 3343222892282389343745799)
              ·
                refine ⟨5014834338423584015618699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3343222892282389343745799 5014834338423584015618699)
                ·
                  refine ⟨7522251507635376023428049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5014834338423584015618699 7522251507635376023428049)
                  ·
                    refine ⟨5641688630726532017571037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7522251507635376023428049 5641688630726532017571037)
                    ·
                      refine ⟨2115633236522449506589139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5641688630726532017571037 2115633236522449506589139)
                      ·
                        rfl

theorem cell23_4120181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 3, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 3, 2, 1, 1, 2, 3].length) (baseStart_4120181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4120181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4120181 prefixEnd_4120181 := by exact prefixLift 4120181
  have htrace : WordTrace (prefixWord ++ tailWord_4120181) baseStart_4120181 baseEnd_4120181 := by
    simpa [prefixWord, tailWord_4120181, baseEnd_4120181] using wordTrace_append hprefix tailTrace_4120181
  have hstable : (prefixWord ++ tailWord_4120181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4120181).length < 2 ^ (prefixWord ++ tailWord_4120181).sum := by decide
  have hdescent : baseEnd_4120181 < baseStart_4120181 := by decide
  rcases family_descends (prefixWord ++ tailWord_4120181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4120187 : List Nat := [1, 1, 1, 1, 1, 4, 5, 3, 1, 3, 2]
def baseStart_4120187 : Nat := 118140960795 + 4120187 * 2 ^ 59
def prefixEnd_4120187 : Nat := 4983230072969 + 3 ^ 40 * 4120187 * 2
def baseEnd_4120187 : Nat := 2115636317406376483114111

theorem tailTrace_4120187 : CollatzResearch.WordTrace tailWord_4120187 prefixEnd_4120187 2115636317406376483114111 := by
  unfold tailWord_4120187
  simp only [CollatzResearch.WordTrace]
  refine ⟨150275565524273645762526815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100183710349515763841684543 150275565524273645762526815)
  ·
    refine ⟨225413348286410468643790223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150275565524273645762526815 225413348286410468643790223)
    ·
      refine ⟨338120022429615702965685335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225413348286410468643790223 338120022429615702965685335)
      ·
        refine ⟨507180033644423554448528003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 338120022429615702965685335 507180033644423554448528003)
        ·
          refine ⟨760770050466635331672792005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 507180033644423554448528003 760770050466635331672792005)
          ·
            refine ⟨142644384462494124688648501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 760770050466635331672792005 142644384462494124688648501)
            ·
              refine ⟨13372911043358824189560797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 142644384462494124688648501 13372911043358824189560797)
              ·
                refine ⟨5014841641259559071085299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13372911043358824189560797 5014841641259559071085299)
                ·
                  refine ⟨7522262461889338606627949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5014841641259559071085299 7522262461889338606627949)
                  ·
                    refine ⟨2820848423208501977485481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7522262461889338606627949 2820848423208501977485481)
                    ·
                      refine ⟨2115636317406376483114111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2820848423208501977485481 2115636317406376483114111)
                      ·
                        rfl

theorem cell23_4120187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 5, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 5, 3, 1, 3, 2].length) (baseStart_4120187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4120187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4120187 prefixEnd_4120187 := by exact prefixLift 4120187
  have htrace : WordTrace (prefixWord ++ tailWord_4120187) baseStart_4120187 baseEnd_4120187 := by
    simpa [prefixWord, tailWord_4120187, baseEnd_4120187] using wordTrace_append hprefix tailTrace_4120187
  have hstable : (prefixWord ++ tailWord_4120187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4120187).length < 2 ^ (prefixWord ++ tailWord_4120187).sum := by decide
  have hdescent : baseEnd_4120187 < baseStart_4120187 := by decide
  rcases family_descends (prefixWord ++ tailWord_4120187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4120270 : List Nat := [4, 1, 1, 1, 3, 1, 1, 2, 4, 5]
def baseStart_4120270 : Nat := 118140960795 + 4120270 * 2 ^ 59
def prefixEnd_4120270 : Nat := 4983230072969 + 3 ^ 40 * 4120270 * 2
def baseEnd_4120270 : Nat := 705226312100233219458743

theorem tailTrace_4120270 : CollatzResearch.WordTrace tailWord_4120270 prefixEnd_4120270 705226312100233219458743 := by
  unfold tailWord_4120270
  simp only [CollatzResearch.WordTrace]
  refine ⟨18784824097871618867224783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 100185728521981967291865509 18784824097871618867224783)
  ·
    refine ⟨28177236146807428300837175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18784824097871618867224783 28177236146807428300837175)
    ·
      refine ⟨42265854220211142451255763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28177236146807428300837175 42265854220211142451255763)
      ·
        refine ⟨63398781330316713676883645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42265854220211142451255763 63398781330316713676883645)
        ·
          refine ⟨23774542998868767628831367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63398781330316713676883645 23774542998868767628831367)
          ·
            refine ⟨35661814498303151443247051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23774542998868767628831367 35661814498303151443247051)
            ·
              refine ⟨53492721747454727164870577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35661814498303151443247051 53492721747454727164870577)
              ·
                refine ⟨40119541310591045373652933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53492721747454727164870577 40119541310591045373652933)
                ·
                  refine ⟨7522413995735821007559925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40119541310591045373652933 7522413995735821007559925)
                  ·
                    refine ⟨705226312100233219458743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7522413995735821007559925 705226312100233219458743)
                    ·
                      rfl

theorem cell23_4120270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 2, 4, 5].length) (baseStart_4120270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4120270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4120270 prefixEnd_4120270 := by exact prefixLift 4120270
  have htrace : WordTrace (prefixWord ++ tailWord_4120270) baseStart_4120270 baseEnd_4120270 := by
    simpa [prefixWord, tailWord_4120270, baseEnd_4120270] using wordTrace_append hprefix tailTrace_4120270
  have hstable : (prefixWord ++ tailWord_4120270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4120270).length < 2 ^ (prefixWord ++ tailWord_4120270).sum := by decide
  have hdescent : baseEnd_4120270 < baseStart_4120270 := by decide
  rcases family_descends (prefixWord ++ tailWord_4120270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4120308 : List Nat := [2, 6, 1, 1, 1, 1, 4, 2, 5]
def baseStart_4120308 : Nat := 118140960795 + 4120308 * 2 ^ 59
def prefixEnd_4120308 : Nat := 4983230072969 + 3 ^ 40 * 4120308 * 2
def baseEnd_4120308 : Nat := 235077605396174501077895

theorem tailTrace_4120308 : CollatzResearch.WordTrace tailWord_4120308 prefixEnd_4120308 235077605396174501077895 := by
  unfold tailWord_4120308
  simp only [CollatzResearch.WordTrace]
  refine ⟨75139989378417641713840789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100186652504556855618454385 75139989378417641713840789)
  ·
    refine ⟨3522187002113326955336287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 75139989378417641713840789 3522187002113326955336287)
    ·
      refine ⟨5283280503169990433004431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3522187002113326955336287 5283280503169990433004431)
      ·
        refine ⟨7924920754754985649506647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5283280503169990433004431 7924920754754985649506647)
        ·
          refine ⟨11887381132132478474259971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7924920754754985649506647 11887381132132478474259971)
          ·
            refine ⟨17831071698198717711389957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11887381132132478474259971 17831071698198717711389957)
            ·
              refine ⟨3343325943412259570885617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17831071698198717711389957 3343325943412259570885617)
              ·
                refine ⟨2507494457559194678164213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3343325943412259570885617 2507494457559194678164213)
                ·
                  refine ⟨235077605396174501077895, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2507494457559194678164213 235077605396174501077895)
                  ·
                    rfl

theorem cell23_4120308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 4, 2, 5].length) (baseStart_4120308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4120308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4120308 prefixEnd_4120308 := by exact prefixLift 4120308
  have htrace : WordTrace (prefixWord ++ tailWord_4120308) baseStart_4120308 baseEnd_4120308 := by
    simpa [prefixWord, tailWord_4120308, baseEnd_4120308] using wordTrace_append hprefix tailTrace_4120308
  have hstable : (prefixWord ++ tailWord_4120308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4120308).length < 2 ^ (prefixWord ++ tailWord_4120308).sum := by decide
  have hdescent : baseEnd_4120308 < baseStart_4120308 := by decide
  rcases family_descends (prefixWord ++ tailWord_4120308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4120324 : List Nat := [2, 3, 2, 2, 1, 3, 1, 1, 2, 4, 2]
def baseStart_4120324 : Nat := 118140960795 + 4120324 * 2 ^ 59
def prefixEnd_4120324 : Nat := 4983230072969 + 3 ^ 40 * 4120324 * 2
def baseEnd_4120324 : Nat := 2115706664256042447100981

theorem tailTrace_4120324 : CollatzResearch.WordTrace tailWord_4120324 prefixEnd_4120324 2115706664256042447100981 := by
  unfold tailWord_4120324
  simp only [CollatzResearch.WordTrace]
  refine ⟨75140281162388659080132013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100187041549851545440176017 75140281162388659080132013)
  ·
    refine ⟨28177605435895747155049505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75140281162388659080132013 28177605435895747155049505)
    ·
      refine ⟨21133204076921810366287129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28177605435895747155049505 21133204076921810366287129)
      ·
        refine ⟨15849903057691357774715347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21133204076921810366287129 15849903057691357774715347)
        ·
          refine ⟨23774854586537036662073021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15849903057691357774715347 23774854586537036662073021)
          ·
            refine ⟨8915570469951388748277383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23774854586537036662073021 8915570469951388748277383)
            ·
              refine ⟨13373355704927083122416075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8915570469951388748277383 13373355704927083122416075)
              ·
                refine ⟨20060033557390624683624113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13373355704927083122416075 20060033557390624683624113)
                ·
                  refine ⟨15045025168042968512718085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20060033557390624683624113 15045025168042968512718085)
                  ·
                    refine ⟨2820942219008056596134641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15045025168042968512718085 2820942219008056596134641)
                    ·
                      refine ⟨2115706664256042447100981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2820942219008056596134641 2115706664256042447100981)
                      ·
                        rfl

theorem cell23_4120324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 1, 1, 2, 4, 2].length) (baseStart_4120324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4120324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4120324 prefixEnd_4120324 := by exact prefixLift 4120324
  have htrace : WordTrace (prefixWord ++ tailWord_4120324) baseStart_4120324 baseEnd_4120324 := by
    simpa [prefixWord, tailWord_4120324, baseEnd_4120324] using wordTrace_append hprefix tailTrace_4120324
  have hstable : (prefixWord ++ tailWord_4120324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4120324).length < 2 ^ (prefixWord ++ tailWord_4120324).sum := by decide
  have hdescent : baseEnd_4120324 < baseStart_4120324 := by decide
  rcases family_descends (prefixWord ++ tailWord_4120324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4120400 : List Nat := [2, 1, 1, 1, 1, 4, 1, 1, 5, 1, 5]
def baseStart_4120400 : Nat := 118140960795 + 4120400 * 2 ^ 59
def prefixEnd_4120400 : Nat := 4983230072969 + 3 ^ 40 * 4120400 * 2
def baseEnd_4120400 : Nat := 2115745688785784149750631

theorem tailTrace_4120400 : CollatzResearch.WordTrace tailWord_4120400 prefixEnd_4120400 2115745688785784149750631 := by
  unfold tailWord_4120400
  simp only [CollatzResearch.WordTrace]
  refine ⟨75141667136250991570015327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100188889515001322093353769 75141667136250991570015327)
  ·
    refine ⟨112712500704376487355022991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75141667136250991570015327 112712500704376487355022991)
    ·
      refine ⟨169068751056564731032534487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112712500704376487355022991 169068751056564731032534487)
      ·
        refine ⟨253603126584847096548801731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169068751056564731032534487 253603126584847096548801731)
        ·
          refine ⟨380404689877270644823202597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 253603126584847096548801731 380404689877270644823202597)
          ·
            refine ⟨71325879351988245904350487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 380404689877270644823202597 71325879351988245904350487)
            ·
              refine ⟨106988819027982368856525731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71325879351988245904350487 106988819027982368856525731)
              ·
                refine ⟨160483228541973553284788597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 106988819027982368856525731 160483228541973553284788597)
                ·
                  refine ⟨15045302675810020620448931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 160483228541973553284788597 15045302675810020620448931)
                  ·
                    refine ⟨22567954013715030930673397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15045302675810020620448931 22567954013715030930673397)
                    ·
                      refine ⟨2115745688785784149750631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22567954013715030930673397 2115745688785784149750631)
                      ·
                        rfl

theorem cell23_4120400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 1, 5, 1, 5].length) (baseStart_4120400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4120400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4120400 prefixEnd_4120400 := by exact prefixLift 4120400
  have htrace : WordTrace (prefixWord ++ tailWord_4120400) baseStart_4120400 baseEnd_4120400 := by
    simpa [prefixWord, tailWord_4120400, baseEnd_4120400] using wordTrace_append hprefix tailTrace_4120400
  have hstable : (prefixWord ++ tailWord_4120400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4120400).length < 2 ^ (prefixWord ++ tailWord_4120400).sum := by decide
  have hdescent : baseEnd_4120400 < baseStart_4120400 := by decide
  rcases family_descends (prefixWord ++ tailWord_4120400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4120417 : List Nat := [1, 2, 3, 1, 1, 1, 6, 1, 1, 1, 5]
def baseStart_4120417 : Nat := 118140960795 + 4120417 * 2 ^ 59
def prefixEnd_4120417 : Nat := 4983230072969 + 3 ^ 40 * 4120417 * 2
def baseEnd_4120417 : Nat := 2115754417956910583238053

theorem tailTrace_4120417 : CollatzResearch.WordTrace tailWord_4120417 prefixEnd_4120417 2115754417956910583238053 := by
  unfold tailWord_4120417
  simp only [CollatzResearch.WordTrace]
  refine ⟨150283954313440395043399505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100189302875626930028933003 150283954313440395043399505)
  ·
    refine ⟨112712965735080296282549629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150283954313440395043399505 112712965735080296282549629)
    ·
      refine ⟨42267362150655111105956111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 112712965735080296282549629 42267362150655111105956111)
      ·
        refine ⟨63401043225982666658934167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42267362150655111105956111 63401043225982666658934167)
        ·
          refine ⟨95101564838973999988401251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63401043225982666658934167 95101564838973999988401251)
          ·
            refine ⟨142652347258460999982601877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95101564838973999988401251 142652347258460999982601877)
            ·
              refine ⟨6686828777740359374184463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 142652347258460999982601877 6686828777740359374184463)
              ·
                refine ⟨10030243166610539061276695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6686828777740359374184463 10030243166610539061276695)
                ·
                  refine ⟨15045364749915808591915043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10030243166610539061276695 15045364749915808591915043)
                  ·
                    refine ⟨22568047124873712887872565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15045364749915808591915043 22568047124873712887872565)
                    ·
                      refine ⟨2115754417956910583238053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22568047124873712887872565 2115754417956910583238053)
                      ·
                        rfl

theorem cell23_4120417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 6, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 6, 1, 1, 1, 5].length) (baseStart_4120417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4120417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4120417 prefixEnd_4120417 := by exact prefixLift 4120417
  have htrace : WordTrace (prefixWord ++ tailWord_4120417) baseStart_4120417 baseEnd_4120417 := by
    simpa [prefixWord, tailWord_4120417, baseEnd_4120417] using wordTrace_append hprefix tailTrace_4120417
  have hstable : (prefixWord ++ tailWord_4120417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4120417).length < 2 ^ (prefixWord ++ tailWord_4120417).sum := by decide
  have hdescent : baseEnd_4120417 < baseStart_4120417 := by decide
  rcases family_descends (prefixWord ++ tailWord_4120417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4120424 : List Nat := [2, 1, 4, 2, 1, 1, 2, 4, 2, 4]
def baseStart_4120424 : Nat := 118140960795 + 4120424 * 2 ^ 59
def prefixEnd_4120424 : Nat := 4983230072969 + 3 ^ 40 * 4120424 * 2
def baseEnd_4120424 : Nat := 705252670773830685283507

theorem tailTrace_4120424 : CollatzResearch.WordTrace tailWord_4120424 prefixEnd_4120424 705252670773830685283507 := by
  unfold tailWord_4120424
  simp only [CollatzResearch.WordTrace]
  refine ⟨75142104812207517619452163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100189473082943356825936217 75142104812207517619452163)
  ·
    refine ⟨112713157218311276429178245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75142104812207517619452163 112713157218311276429178245)
    ·
      refine ⟨21133716978433364330470921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 112713157218311276429178245 21133716978433364330470921)
      ·
        refine ⟨15850287733825023247853191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21133716978433364330470921 15850287733825023247853191)
        ·
          refine ⟨23775431600737534871779787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15850287733825023247853191 23775431600737534871779787)
          ·
            refine ⟨35663147401106302307669681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23775431600737534871779787 35663147401106302307669681)
            ·
              refine ⟨26747360550829726730752261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35663147401106302307669681 26747360550829726730752261)
              ·
                refine ⟨5015130103280573762016049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26747360550829726730752261 5015130103280573762016049)
                ·
                  refine ⟨3761347577460430321512037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5015130103280573762016049 3761347577460430321512037)
                  ·
                    refine ⟨705252670773830685283507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3761347577460430321512037 705252670773830685283507)
                    ·
                      rfl

theorem cell23_4120424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 2, 4, 2, 4].length) (baseStart_4120424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4120424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4120424 prefixEnd_4120424 := by exact prefixLift 4120424
  have htrace : WordTrace (prefixWord ++ tailWord_4120424) baseStart_4120424 baseEnd_4120424 := by
    simpa [prefixWord, tailWord_4120424, baseEnd_4120424] using wordTrace_append hprefix tailTrace_4120424
  have hstable : (prefixWord ++ tailWord_4120424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4120424).length < 2 ^ (prefixWord ++ tailWord_4120424).sum := by decide
  have hdescent : baseEnd_4120424 < baseStart_4120424 := by decide
  rcases family_descends (prefixWord ++ tailWord_4120424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4120437 : List Nat := [1, 3, 4, 1, 1, 1, 4, 8]
def baseStart_4120437 : Nat := 118140960795 + 4120437 * 2 ^ 59
def prefixEnd_4120437 : Nat := 4983230072969 + 3 ^ 40 * 4120437 * 2
def baseEnd_4120437 : Nat := 78361655095185203888443

theorem tailTrace_4120437 : CollatzResearch.WordTrace tailWord_4120437 prefixEnd_4120437 78361655095185203888443 := by
  unfold tailWord_4120437
  simp only [CollatzResearch.WordTrace]
  refine ⟨150284683773367938459127565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100189789182245292306085043 150284683773367938459127565)
  ·
    refine ⟨56356756415012976922172837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 150284683773367938459127565 56356756415012976922172837)
    ·
      refine ⟨10566891827814933172907407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 56356756415012976922172837 10566891827814933172907407)
      ·
        refine ⟨15850337741722399759361111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10566891827814933172907407 15850337741722399759361111)
        ·
          refine ⟨23775506612583599639041667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15850337741722399759361111 23775506612583599639041667)
          ·
            refine ⟨35663259918875399458562501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23775506612583599639041667 35663259918875399458562501)
            ·
              refine ⟨6686861234789137398480469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35663259918875399458562501 6686861234789137398480469)
              ·
                refine ⟨78361655095185203888443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6686861234789137398480469 78361655095185203888443)
                ·
                  rfl

theorem cell23_4120437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 4, 8].length) (baseStart_4120437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4120437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4120437 prefixEnd_4120437 := by exact prefixLift 4120437
  have htrace : WordTrace (prefixWord ++ tailWord_4120437) baseStart_4120437 baseEnd_4120437 := by
    simpa [prefixWord, tailWord_4120437, baseEnd_4120437] using wordTrace_append hprefix tailTrace_4120437
  have hstable : (prefixWord ++ tailWord_4120437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4120437).length < 2 ^ (prefixWord ++ tailWord_4120437).sum := by decide
  have hdescent : baseEnd_4120437 < baseStart_4120437 := by decide
  rcases family_descends (prefixWord ++ tailWord_4120437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4120447 : List Nat := [1, 1, 2, 2, 1, 1, 3, 5, 1, 3, 3]
def baseStart_4120447 : Nat := 118140960795 + 4120447 * 2 ^ 59
def prefixEnd_4120447 : Nat := 4983230072969 + 3 ^ 40 * 4120447 * 2
def baseEnd_4120447 : Nat := 2115769822376545465862915

theorem tailTrace_4120447 : CollatzResearch.WordTrace tailWord_4120447 prefixEnd_4120447 2115769822376545465862915 := by
  unfold tailWord_4120447
  simp only [CollatzResearch.WordTrace]
  refine ⟨150285048503331710166991595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100190032335554473444661063 150285048503331710166991595)
  ·
    refine ⟨225427572754997565250487393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150285048503331710166991595 225427572754997565250487393)
    ·
      refine ⟨169070679566248173937865545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 225427572754997565250487393 169070679566248173937865545)
      ·
        refine ⟨126803009674686130453399159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 169070679566248173937865545 126803009674686130453399159)
        ·
          refine ⟨190204514512029195680098739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126803009674686130453399159 190204514512029195680098739)
          ·
            refine ⟨285306771768043793520148109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 190204514512029195680098739 285306771768043793520148109)
            ·
              refine ⟨106990039413016422570055541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 285306771768043793520148109 106990039413016422570055541)
              ·
                refine ⟨10030316194970289615942707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 106990039413016422570055541 10030316194970289615942707)
                ·
                  refine ⟨15045474292455434423914061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10030316194970289615942707 15045474292455434423914061)
                  ·
                    refine ⟨5642052859670787908967773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15045474292455434423914061 5642052859670787908967773)
                    ·
                      refine ⟨2115769822376545465862915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5642052859670787908967773 2115769822376545465862915)
                      ·
                        rfl

theorem cell23_4120447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 5, 1, 3, 3].length) (baseStart_4120447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4120447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4120447 prefixEnd_4120447 := by exact prefixLift 4120447
  have htrace : WordTrace (prefixWord ++ tailWord_4120447) baseStart_4120447 baseEnd_4120447 := by
    simpa [prefixWord, tailWord_4120447, baseEnd_4120447] using wordTrace_append hprefix tailTrace_4120447
  have hstable : (prefixWord ++ tailWord_4120447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4120447).length < 2 ^ (prefixWord ++ tailWord_4120447).sum := by decide
  have hdescent : baseEnd_4120447 < baseStart_4120447 := by decide
  rcases family_descends (prefixWord ++ tailWord_4120447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4120451 : List Nat := [1, 1, 1, 3, 4, 4, 1, 2, 1, 2, 3]
def baseStart_4120451 : Nat := 118140960795 + 4120451 * 2 ^ 59
def prefixEnd_4120451 : Nat := 4983230072969 + 3 ^ 40 * 4120451 * 2
def baseEnd_4120451 : Nat := 2115771876299163450212897

theorem tailTrace_4120451 : CollatzResearch.WordTrace tailWord_4120451 prefixEnd_4120451 2115771876299163450212897 := by
  unfold tailWord_4120451
  simp only [CollatzResearch.WordTrace]
  refine ⟨150285194395317218850137207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100190129596878145900091471 150285194395317218850137207)
  ·
    refine ⟨225427791592975828275205811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150285194395317218850137207 225427791592975828275205811)
    ·
      refine ⟨338141687389463742412808717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225427791592975828275205811 338141687389463742412808717)
      ·
        refine ⟨126803132771048903404803269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 338141687389463742412808717 126803132771048903404803269)
        ·
          refine ⟨23775587394571669388400613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 126803132771048903404803269 23775587394571669388400613)
          ·
            refine ⟨4457922636482188010325115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23775587394571669388400613 4457922636482188010325115)
            ·
              refine ⟨6686883954723282015487673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4457922636482188010325115 6686883954723282015487673)
              ·
                refine ⟨5015162966042461511615755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6686883954723282015487673 5015162966042461511615755)
                ·
                  refine ⟨7522744449063692267423633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5015162966042461511615755 7522744449063692267423633)
                  ·
                    refine ⟨5642058336797769200567725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7522744449063692267423633 5642058336797769200567725)
                    ·
                      refine ⟨2115771876299163450212897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5642058336797769200567725 2115771876299163450212897)
                      ·
                        rfl

theorem cell23_4120451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 4, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 4, 1, 2, 1, 2, 3].length) (baseStart_4120451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4120451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4120451 prefixEnd_4120451 := by exact prefixLift 4120451
  have htrace : WordTrace (prefixWord ++ tailWord_4120451) baseStart_4120451 baseEnd_4120451 := by
    simpa [prefixWord, tailWord_4120451, baseEnd_4120451] using wordTrace_append hprefix tailTrace_4120451
  have hstable : (prefixWord ++ tailWord_4120451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4120451).length < 2 ^ (prefixWord ++ tailWord_4120451).sum := by decide
  have hdescent : baseEnd_4120451 < baseStart_4120451 := by decide
  rcases family_descends (prefixWord ++ tailWord_4120451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4120468 : List Nat := [2, 4, 2, 1, 1, 3, 3, 1, 1, 2, 3]
def baseStart_4120468 : Nat := 118140960795 + 4120468 * 2 ^ 59
def prefixEnd_4120468 : Nat := 4983230072969 + 3 ^ 40 * 4120468 * 2
def baseEnd_4120468 : Nat := 2115780605470289883700319

theorem tailTrace_4120468 : CollatzResearch.WordTrace tailWord_4120468 prefixEnd_4120468 2115780605470289883700319 := by
  unfold tailWord_4120468
  simp only [CollatzResearch.WordTrace]
  refine ⟨75142907218127815376753029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100190542957503753835670705 75142907218127815376753029)
  ·
    refine ⟨14089295103398965383141193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 75142907218127815376753029 14089295103398965383141193)
    ·
      refine ⟨10566971327549224037355895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14089295103398965383141193 10566971327549224037355895)
      ·
        refine ⟨15850456991323836056033843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10566971327549224037355895 15850456991323836056033843)
        ·
          refine ⟨23775685486985754084050765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15850456991323836056033843 23775685486985754084050765)
          ·
            refine ⟨8915882057619657781519037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23775685486985754084050765 8915882057619657781519037)
            ·
              refine ⟨3343455771607371668069639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8915882057619657781519037 3343455771607371668069639)
              ·
                refine ⟨5015183657411057502104459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3343455771607371668069639 5015183657411057502104459)
                ·
                  refine ⟨7522775486116586253156689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5015183657411057502104459 7522775486116586253156689)
                  ·
                    refine ⟨5642081614587439689867517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7522775486116586253156689 5642081614587439689867517)
                    ·
                      refine ⟨2115780605470289883700319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5642081614587439689867517 2115780605470289883700319)
                      ·
                        rfl

theorem cell23_4120468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 3, 1, 1, 2, 3].length) (baseStart_4120468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4120468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4120468 prefixEnd_4120468 := by exact prefixLift 4120468
  have htrace : WordTrace (prefixWord ++ tailWord_4120468) baseStart_4120468 baseEnd_4120468 := by
    simpa [prefixWord, tailWord_4120468, baseEnd_4120468] using wordTrace_append hprefix tailTrace_4120468
  have hstable : (prefixWord ++ tailWord_4120468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4120468).length < 2 ^ (prefixWord ++ tailWord_4120468).sum := by decide
  have hdescent : baseEnd_4120468 < baseStart_4120468 := by decide
  rcases family_descends (prefixWord ++ tailWord_4120468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4120488 : List Nat := [2, 1, 6, 2, 2, 1, 1, 8]
def baseStart_4120488 : Nat := 118140960795 + 4120488 * 2 ^ 59
def prefixEnd_4120488 : Nat := 4983230072969 + 3 ^ 40 * 4120488 * 2
def baseEnd_4120488 : Nat := 78362625003088140942601

theorem tailTrace_4120488 : CollatzResearch.WordTrace tailWord_4120488 prefixEnd_4120488 78362625003088140942601 := by
  unfold tailWord_4120488
  simp only [CollatzResearch.WordTrace]
  refine ⟨75143271948091587084617059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100191029264122116112822745 75143271948091587084617059)
  ·
    refine ⟨112714907922137380626925589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75143271948091587084617059 112714907922137380626925589)
    ·
      refine ⟨5283511308850189716887137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 112714907922137380626925589 5283511308850189716887137)
      ·
        refine ⟨3962633481637642287665353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5283511308850189716887137 3962633481637642287665353)
        ·
          refine ⟨2971975111228231715749015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3962633481637642287665353 2971975111228231715749015)
          ·
            refine ⟨4457962666842347573623523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2971975111228231715749015 4457962666842347573623523)
            ·
              refine ⟨6686944000263521360435285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4457962666842347573623523 6686944000263521360435285)
              ·
                refine ⟨78362625003088140942601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6686944000263521360435285 78362625003088140942601)
                ·
                  rfl

theorem cell23_4120488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 2, 1, 1, 8].length) (baseStart_4120488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4120488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4120488 prefixEnd_4120488 := by exact prefixLift 4120488
  have htrace : WordTrace (prefixWord ++ tailWord_4120488) baseStart_4120488 baseEnd_4120488 := by
    simpa [prefixWord, tailWord_4120488, baseEnd_4120488] using wordTrace_append hprefix tailTrace_4120488
  have hstable : (prefixWord ++ tailWord_4120488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4120488).length < 2 ^ (prefixWord ++ tailWord_4120488).sum := by decide
  have hdescent : baseEnd_4120488 < baseStart_4120488 := by decide
  rcases family_descends (prefixWord ++ tailWord_4120488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4120497 : List Nat := [1, 2, 2, 4, 2, 1, 1, 1, 1, 8]
def baseStart_4120497 : Nat := 118140960795 + 4120497 * 2 ^ 59
def prefixEnd_4120497 : Nat := 4983230072969 + 3 ^ 40 * 4120497 * 2
def baseEnd_4120497 : Nat := 705265165469756756745895

theorem tailTrace_4120497 : CollatzResearch.WordTrace tailWord_4120497 prefixEnd_4120497 705265165469756756745895 := by
  unfold tailWord_4120497
  simp only [CollatzResearch.WordTrace]
  refine ⟨150286872153150568706311745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100191248102100379137541163 150286872153150568706311745)
  ·
    refine ⟨112715154114862926529733809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150286872153150568706311745 112715154114862926529733809)
    ·
      refine ⟨84536365586147194897300357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112715154114862926529733809 84536365586147194897300357)
      ·
        refine ⟨15850568547402599043243817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 84536365586147194897300357 15850568547402599043243817)
        ·
          refine ⟨11887926410551949282432863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15850568547402599043243817 11887926410551949282432863)
          ·
            refine ⟨17831889615827923923649295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11887926410551949282432863 17831889615827923923649295)
            ·
              refine ⟨26747834423741885885473943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17831889615827923923649295 26747834423741885885473943)
              ·
                refine ⟨40121751635612828828210915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26747834423741885885473943 40121751635612828828210915)
                ·
                  refine ⟨60182627453419243242316373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40121751635612828828210915 60182627453419243242316373)
                  ·
                    refine ⟨705265165469756756745895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 60182627453419243242316373 705265165469756756745895)
                    ·
                      rfl

theorem cell23_4120497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 1, 1, 1, 8].length) (baseStart_4120497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4120497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4120497 prefixEnd_4120497 := by exact prefixLift 4120497
  have htrace : WordTrace (prefixWord ++ tailWord_4120497) baseStart_4120497 baseEnd_4120497 := by
    simpa [prefixWord, tailWord_4120497, baseEnd_4120497] using wordTrace_append hprefix tailTrace_4120497
  have hstable : (prefixWord ++ tailWord_4120497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4120497).length < 2 ^ (prefixWord ++ tailWord_4120497).sum := by decide
  have hdescent : baseEnd_4120497 < baseStart_4120497 := by decide
  rcases family_descends (prefixWord ++ tailWord_4120497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4120538 : List Nat := [3, 1, 1, 2, 5, 1, 1, 1, 4, 2, 2]
def baseStart_4120538 : Nat := 118140960795 + 4120538 * 2 ^ 59
def prefixEnd_4120538 : Nat := 4983230072969 + 3 ^ 40 * 4120538 * 2
def baseEnd_4120538 : Nat := 2115816549116104609824997

theorem tailTrace_4120538 : CollatzResearch.WordTrace tailWord_4120538 prefixEnd_4120538 2115816549116104609824997 := by
  unfold tailWord_4120538
  simp only [CollatzResearch.WordTrace]
  refine ⟨37572091886500508177138567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100192245030668021805702845 37572091886500508177138567)
  ·
    refine ⟨56358137829750762265707851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37572091886500508177138567 56358137829750762265707851)
    ·
      refine ⟨84537206744626143398561777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56358137829750762265707851 84537206744626143398561777)
      ·
        refine ⟨63402905058469607548921333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84537206744626143398561777 63402905058469607548921333)
        ·
          refine ⟨5944022349231525707711375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 63402905058469607548921333 5944022349231525707711375)
          ·
            refine ⟨8916033523847288561567063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5944022349231525707711375 8916033523847288561567063)
            ·
              refine ⟨13374050285770932842350595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8916033523847288561567063 13374050285770932842350595)
              ·
                refine ⟨20061075428656399263525893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13374050285770932842350595 20061075428656399263525893)
                ·
                  refine ⟨3761451642873074861911105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20061075428656399263525893 3761451642873074861911105)
                  ·
                    refine ⟨2821088732154806146433329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3761451642873074861911105 2821088732154806146433329)
                    ·
                      refine ⟨2115816549116104609824997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2821088732154806146433329 2115816549116104609824997)
                      ·
                        rfl

theorem cell23_4120538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 1, 1, 4, 2, 2].length) (baseStart_4120538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4120538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4120538 prefixEnd_4120538 := by exact prefixLift 4120538
  have htrace : WordTrace (prefixWord ++ tailWord_4120538) baseStart_4120538 baseEnd_4120538 := by
    simpa [prefixWord, tailWord_4120538, baseEnd_4120538] using wordTrace_append hprefix tailTrace_4120538
  have hstable : (prefixWord ++ tailWord_4120538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4120538).length < 2 ^ (prefixWord ++ tailWord_4120538).sum := by decide
  have hdescent : baseEnd_4120538 < baseStart_4120538 := by decide
  rcases family_descends (prefixWord ++ tailWord_4120538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4120554 : List Nat := [3, 1, 3, 1, 2, 1, 1, 3, 2, 3, 3]
def baseStart_4120554 : Nat := 118140960795 + 4120554 * 2 ^ 59
def prefixEnd_4120554 : Nat := 4983230072969 + 3 ^ 40 * 4120554 * 2
def baseEnd_4120554 : Nat := 2115824764806576547224923

theorem tailTrace_4120554 : CollatzResearch.WordTrace tailWord_4120554 prefixEnd_4120554 2115824764806576547224923 := by
  unfold tailWord_4120554
  simp only [CollatzResearch.WordTrace]
  refine ⟨37572237778486016860284179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100192634075962711627424477 37572237778486016860284179)
  ·
    refine ⟨56358356667729025290426269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37572237778486016860284179 56358356667729025290426269)
    ·
      refine ⟨21134383750398384483909851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56358356667729025290426269 21134383750398384483909851)
      ·
        refine ⟨31701575625597576725864777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21134383750398384483909851 31701575625597576725864777)
        ·
          refine ⟨23776181719198182544398583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31701575625597576725864777 23776181719198182544398583)
          ·
            refine ⟨35664272578797273816597875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23776181719198182544398583 35664272578797273816597875)
            ·
              refine ⟨53496408868195910724896813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35664272578797273816597875 53496408868195910724896813)
              ·
                refine ⟨20061153325573466521836305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53496408868195910724896813 20061153325573466521836305)
                ·
                  refine ⟨15045864994180099891377229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20061153325573466521836305 15045864994180099891377229)
                  ·
                    refine ⟨5642199372817537459266461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15045864994180099891377229 5642199372817537459266461)
                    ·
                      refine ⟨2115824764806576547224923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5642199372817537459266461 2115824764806576547224923)
                      ·
                        rfl

theorem cell23_4120554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 3, 2, 3, 3].length) (baseStart_4120554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4120554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4120554 prefixEnd_4120554 := by exact prefixLift 4120554
  have htrace : WordTrace (prefixWord ++ tailWord_4120554) baseStart_4120554 baseEnd_4120554 := by
    simpa [prefixWord, tailWord_4120554, baseEnd_4120554] using wordTrace_append hprefix tailTrace_4120554
  have hstable : (prefixWord ++ tailWord_4120554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4120554).length < 2 ^ (prefixWord ++ tailWord_4120554).sum := by decide
  have hdescent : baseEnd_4120554 < baseStart_4120554 := by decide
  rcases family_descends (prefixWord ++ tailWord_4120554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4120664 : List Nat := [2, 1, 2, 2, 1, 4, 1, 2, 3, 5]
def baseStart_4120664 : Nat := 118140960795 + 4120664 * 2 ^ 59
def prefixEnd_4120664 : Nat := 4983230072969 + 3 ^ 40 * 4120664 * 2
def baseEnd_4120664 : Nat := 705293749226190372283139

theorem tailTrace_4120664 : CollatzResearch.WordTrace tailWord_4120664 prefixEnd_4120664 705293749226190372283139 := by
  unfold tailWord_4120664
  simp only [CollatzResearch.WordTrace]
  refine ⟨75146481571772778113820523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100195308762363704151760697 75146481571772778113820523)
  ·
    refine ⟨112719722357659167170730785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75146481571772778113820523 112719722357659167170730785)
    ·
      refine ⟨84539791768244375378048089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112719722357659167170730785 84539791768244375378048089)
      ·
        refine ⟨63404843826183281533536067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84539791768244375378048089 63404843826183281533536067)
        ·
          refine ⟨95107265739274922300304101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63404843826183281533536067 95107265739274922300304101)
          ·
            refine ⟨17832612326114047931307019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 95107265739274922300304101 17832612326114047931307019)
            ·
              refine ⟨26748918489171071896960529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17832612326114047931307019 26748918489171071896960529)
              ·
                refine ⟨20061688866878303922720397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26748918489171071896960529 20061688866878303922720397)
                ·
                  refine ⟨7523133325079363971020149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20061688866878303922720397 7523133325079363971020149)
                  ·
                    refine ⟨705293749226190372283139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7523133325079363971020149 705293749226190372283139)
                    ·
                      rfl

theorem cell23_4120664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 1, 2, 3, 5].length) (baseStart_4120664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4120664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4120664 prefixEnd_4120664 := by exact prefixLift 4120664
  have htrace : WordTrace (prefixWord ++ tailWord_4120664) baseStart_4120664 baseEnd_4120664 := by
    simpa [prefixWord, tailWord_4120664, baseEnd_4120664] using wordTrace_append hprefix tailTrace_4120664
  have hstable : (prefixWord ++ tailWord_4120664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4120664).length < 2 ^ (prefixWord ++ tailWord_4120664).sum := by decide
  have hdescent : baseEnd_4120664 < baseStart_4120664 := by decide
  rcases family_descends (prefixWord ++ tailWord_4120664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4120688 : List Nat := [2, 1, 1, 1, 5, 2, 3, 1, 2, 3, 2]
def baseStart_4120688 : Nat := 118140960795 + 4120688 * 2 ^ 59
def prefixEnd_4120688 : Nat := 4983230072969 + 3 ^ 40 * 4120688 * 2
def baseEnd_4120688 : Nat := 2115893571214279022949307

theorem tailTrace_4120688 : CollatzResearch.WordTrace tailWord_4120688 prefixEnd_4120688 2115893571214279022949307 := by
  unfold tailWord_4120688
  simp only [CollatzResearch.WordTrace]
  refine ⟨75146919247729304163257359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100195892330305738884343145 75146919247729304163257359)
  ·
    refine ⟨112720378871593956244886039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75146919247729304163257359 112720378871593956244886039)
    ·
      refine ⟨169080568307390934367329059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112720378871593956244886039 169080568307390934367329059)
      ·
        refine ⟨253620852461086401550993589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169080568307390934367329059 253620852461086401550993589)
        ·
          refine ⟨23776954918226850145405649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 253620852461086401550993589 23776954918226850145405649)
          ·
            refine ⟨17832716188670137609054237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23776954918226850145405649 17832716188670137609054237)
            ·
              refine ⟨6687268570751301603395339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17832716188670137609054237 6687268570751301603395339)
              ·
                refine ⟨10030902856126952405093009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6687268570751301603395339 10030902856126952405093009)
                ·
                  refine ⟨7523177142095214303819757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10030902856126952405093009 7523177142095214303819757)
                  ·
                    refine ⟨2821191428285705363932409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7523177142095214303819757 2821191428285705363932409)
                    ·
                      refine ⟨2115893571214279022949307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2821191428285705363932409 2115893571214279022949307)
                      ·
                        rfl

theorem cell23_4120688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 3, 1, 2, 3, 2].length) (baseStart_4120688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4120688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4120688 prefixEnd_4120688 := by exact prefixLift 4120688
  have htrace : WordTrace (prefixWord ++ tailWord_4120688) baseStart_4120688 baseEnd_4120688 := by
    simpa [prefixWord, tailWord_4120688, baseEnd_4120688] using wordTrace_append hprefix tailTrace_4120688
  have hstable : (prefixWord ++ tailWord_4120688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4120688).length < 2 ^ (prefixWord ++ tailWord_4120688).sum := by decide
  have hdescent : baseEnd_4120688 < baseStart_4120688 := by decide
  rcases family_descends (prefixWord ++ tailWord_4120688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4120695 : List Nat := [1, 1, 3, 1, 1, 6, 2, 3, 1, 1, 3]
def baseStart_4120695 : Nat := 118140960795 + 4120695 * 2 ^ 59
def prefixEnd_4120695 : Nat := 4983230072969 + 3 ^ 40 * 4120695 * 2
def baseEnd_4120695 : Nat := 2115897165578860495561775

theorem tailTrace_4120695 : CollatzResearch.WordTrace tailWord_4120695 prefixEnd_4120695 2115897165578860495561775 := by
  unfold tailWord_4120695
  simp only [CollatzResearch.WordTrace]
  refine ⟨150294093806433248522019539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100196062537622165681346359 150294093806433248522019539)
  ·
    refine ⟨225441140709649872783029309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150294093806433248522019539 225441140709649872783029309)
    ·
      refine ⟨84540427766118702293635991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 225441140709649872783029309 84540427766118702293635991)
      ·
        refine ⟨126810641649178053440453987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84540427766118702293635991 126810641649178053440453987)
        ·
          refine ⟨190215962473767080160680981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126810641649178053440453987 190215962473767080160680981)
          ·
            refine ⟨8916373240957831882531921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 190215962473767080160680981 8916373240957831882531921)
            ·
              refine ⟨6687279930718373911898941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8916373240957831882531921 6687279930718373911898941)
              ·
                refine ⟨2507729974019390216962103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6687279930718373911898941 2507729974019390216962103)
                ·
                  refine ⟨3761594961029085325443155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2507729974019390216962103 3761594961029085325443155)
                  ·
                    refine ⟨5642392441543627988164733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3761594961029085325443155 5642392441543627988164733)
                    ·
                      refine ⟨2115897165578860495561775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5642392441543627988164733 2115897165578860495561775)
                      ·
                        rfl

theorem cell23_4120695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 2, 3, 1, 1, 3].length) (baseStart_4120695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4120695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4120695 prefixEnd_4120695 := by exact prefixLift 4120695
  have htrace : WordTrace (prefixWord ++ tailWord_4120695) baseStart_4120695 baseEnd_4120695 := by
    simpa [prefixWord, tailWord_4120695, baseEnd_4120695] using wordTrace_append hprefix tailTrace_4120695
  have hstable : (prefixWord ++ tailWord_4120695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4120695).length < 2 ^ (prefixWord ++ tailWord_4120695).sum := by decide
  have hdescent : baseEnd_4120695 < baseStart_4120695 := by decide
  rcases family_descends (prefixWord ++ tailWord_4120695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4120704 : List Nat := [2, 1, 1, 2, 1, 3, 1, 5, 1, 1, 5]
def baseStart_4120704 : Nat := 118140960795 + 4120704 * 2 ^ 59
def prefixEnd_4120704 : Nat := 4983230072969 + 3 ^ 40 * 4120704 * 2
def baseEnd_4120704 : Nat := 2115901786904750960349233

theorem tailTrace_4120704 : CollatzResearch.WordTrace tailWord_4120704 prefixEnd_4120704 2115901786904750960349233 := by
  unfold tailWord_4120704
  simp only [CollatzResearch.WordTrace]
  refine ⟨75147211031700321529548583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100196281375600428706064777 75147211031700321529548583)
  ·
    refine ⟨112720816547550482294322875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75147211031700321529548583 112720816547550482294322875)
    ·
      refine ⟨169081224821325723441484313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112720816547550482294322875 169081224821325723441484313)
      ·
        refine ⟨126810918615994292581113235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 169081224821325723441484313 126810918615994292581113235)
        ·
          refine ⟨190216377923991438871669853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126810918615994292581113235 190216377923991438871669853)
          ·
            refine ⟨71331141721496789576876195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 190216377923991438871669853 71331141721496789576876195)
            ·
              refine ⟨106996712582245184365314293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71331141721496789576876195 106996712582245184365314293)
              ·
                refine ⟨10030941804585486034248215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 106996712582245184365314293 10030941804585486034248215)
                ·
                  refine ⟨15046412706878229051372323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10030941804585486034248215 15046412706878229051372323)
                  ·
                    refine ⟨22569619060317343577058485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15046412706878229051372323 22569619060317343577058485)
                    ·
                      refine ⟨2115901786904750960349233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22569619060317343577058485 2115901786904750960349233)
                      ·
                        rfl

theorem cell23_4120704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 5, 1, 1, 5].length) (baseStart_4120704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4120704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4120704 prefixEnd_4120704 := by exact prefixLift 4120704
  have htrace : WordTrace (prefixWord ++ tailWord_4120704) baseStart_4120704 baseEnd_4120704 := by
    simpa [prefixWord, tailWord_4120704, baseEnd_4120704] using wordTrace_append hprefix tailTrace_4120704
  have hstable : (prefixWord ++ tailWord_4120704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4120704).length < 2 ^ (prefixWord ++ tailWord_4120704).sum := by decide
  have hdescent : baseEnd_4120704 < baseStart_4120704 := by decide
  rcases family_descends (prefixWord ++ tailWord_4120704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4120728 : List Nat := [2, 1, 2, 4, 3, 2, 1, 1, 1, 6]
def baseStart_4120728 : Nat := 118140960795 + 4120728 * 2 ^ 59
def prefixEnd_4120728 : Nat := 4983230072969 + 3 ^ 40 * 4120728 * 2
def baseEnd_4120728 : Nat := 705304703480152955483041

theorem tailTrace_4120728 : CollatzResearch.WordTrace tailWord_4120728 prefixEnd_4120728 705304703480152955483041 := by
  unfold tailWord_4120728
  simp only [CollatzResearch.WordTrace]
  refine ⟨75147648707656847578985419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100196864943542463438647225 75147648707656847578985419)
  ·
    refine ⟨112721473061485271368478129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75147648707656847578985419 112721473061485271368478129)
    ·
      refine ⟨84541104796113953526358597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112721473061485271368478129 84541104796113953526358597)
      ·
        refine ⟨15851457149271366286192237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 84541104796113953526358597 15851457149271366286192237)
        ·
          refine ⟨5944296430976762357322089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15851457149271366286192237 5944296430976762357322089)
          ·
            refine ⟨4458222323232571767991567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5944296430976762357322089 4458222323232571767991567)
            ·
              refine ⟨6687333484848857651987351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4458222323232571767991567 6687333484848857651987351)
              ·
                refine ⟨10031000227273286477981027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6687333484848857651987351 10031000227273286477981027)
                ·
                  refine ⟨15046500340909929716971541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10031000227273286477981027 15046500340909929716971541)
                  ·
                    refine ⟨705304703480152955483041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15046500340909929716971541 705304703480152955483041)
                    ·
                      rfl

theorem cell23_4120728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 2, 1, 1, 1, 6].length) (baseStart_4120728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4120728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4120728 prefixEnd_4120728 := by exact prefixLift 4120728
  have htrace : WordTrace (prefixWord ++ tailWord_4120728) baseStart_4120728 baseEnd_4120728 := by
    simpa [prefixWord, tailWord_4120728, baseEnd_4120728] using wordTrace_append hprefix tailTrace_4120728
  have hstable : (prefixWord ++ tailWord_4120728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4120728).length < 2 ^ (prefixWord ++ tailWord_4120728).sum := by decide
  have hdescent : baseEnd_4120728 < baseStart_4120728 := by decide
  rcases family_descends (prefixWord ++ tailWord_4120728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4120735 : List Nat := [1, 1, 2, 6, 1, 1, 2, 2, 3, 2, 2]
def baseStart_4120735 : Nat := 118140960795 + 4120735 * 2 ^ 59
def prefixEnd_4120735 : Nat := 4983230072969 + 3 ^ 40 * 4120735 * 2
def baseEnd_4120735 : Nat := 2115917704805040339061591

theorem tailTrace_4120735 : CollatzResearch.WordTrace tailWord_4120735 prefixEnd_4120735 2115917704805040339061591 := by
  unfold tailWord_4120735
  simp only [CollatzResearch.WordTrace]
  refine ⟨150295552726288335353475659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100197035150858890235650439 150295552726288335353475659)
  ·
    refine ⟨225443329089432503030213489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150295552726288335353475659 225443329089432503030213489)
    ·
      refine ⟨169082496817074377272660117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 225443329089432503030213489 169082496817074377272660117)
      ·
        refine ⟨7925742038300361434655943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 169082496817074377272660117 7925742038300361434655943)
        ·
          refine ⟨11888613057450542151983915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7925742038300361434655943 11888613057450542151983915)
          ·
            refine ⟨17832919586175813227975873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11888613057450542151983915 17832919586175813227975873)
            ·
              refine ⟨13374689689631859920981905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17832919586175813227975873 13374689689631859920981905)
              ·
                refine ⟨10031017267223894940736429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13374689689631859920981905 10031017267223894940736429)
                ·
                  refine ⟨3761631475208960602776161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10031017267223894940736429 3761631475208960602776161)
                  ·
                    refine ⟨2821223606406720452082121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3761631475208960602776161 2821223606406720452082121)
                    ·
                      refine ⟨2115917704805040339061591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2821223606406720452082121 2115917704805040339061591)
                      ·
                        rfl

theorem cell23_4120735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 2, 2, 3, 2, 2].length) (baseStart_4120735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4120735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4120735 prefixEnd_4120735 := by exact prefixLift 4120735
  have htrace : WordTrace (prefixWord ++ tailWord_4120735) baseStart_4120735 baseEnd_4120735 := by
    simpa [prefixWord, tailWord_4120735, baseEnd_4120735] using wordTrace_append hprefix tailTrace_4120735
  have hstable : (prefixWord ++ tailWord_4120735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4120735).length < 2 ^ (prefixWord ++ tailWord_4120735).sum := by decide
  have hdescent : baseEnd_4120735 < baseStart_4120735 := by decide
  rcases family_descends (prefixWord ++ tailWord_4120735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4120746 : List Nat := [3, 1, 5, 1, 3, 1, 1, 3, 1, 1, 3]
def baseStart_4120746 : Nat := 118140960795 + 4120746 * 2 ^ 59
def prefixEnd_4120746 : Nat := 4983230072969 + 3 ^ 40 * 4120746 * 2
def baseEnd_4120746 : Nat := 2115923353092239796024041

theorem tailTrace_4120746 : CollatzResearch.WordTrace tailWord_4120746 prefixEnd_4120746 2115923353092239796024041 := by
  unfold tailWord_4120746
  simp only [CollatzResearch.WordTrace]
  refine ⟨37573988482312121058031523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100197302619498989488084061 37573988482312121058031523)
  ·
    refine ⟨56360982723468181587047285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37573988482312121058031523 56360982723468181587047285)
    ·
      refine ⟨5283842130325142023785683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 56360982723468181587047285 5283842130325142023785683)
      ·
        refine ⟨7925763195487713035678525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5283842130325142023785683 7925763195487713035678525)
        ·
          refine ⟨2972161198307892388379447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7925763195487713035678525 2972161198307892388379447)
          ·
            refine ⟨4458241797461838582569171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2972161198307892388379447 4458241797461838582569171)
            ·
              refine ⟨6687362696192757873853757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4458241797461838582569171 6687362696192757873853757)
              ·
                refine ⟨2507761011072284202695159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6687362696192757873853757 2507761011072284202695159)
                ·
                  refine ⟨3761641516608426304042739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2507761011072284202695159 3761641516608426304042739)
                  ·
                    refine ⟨5642462274912639456064109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3761641516608426304042739 5642462274912639456064109)
                    ·
                      refine ⟨2115923353092239796024041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5642462274912639456064109 2115923353092239796024041)
                      ·
                        rfl

theorem cell23_4120746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 3, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 3, 1, 1, 3, 1, 1, 3].length) (baseStart_4120746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4120746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4120746 prefixEnd_4120746 := by exact prefixLift 4120746
  have htrace : WordTrace (prefixWord ++ tailWord_4120746) baseStart_4120746 baseEnd_4120746 := by
    simpa [prefixWord, tailWord_4120746, baseEnd_4120746] using wordTrace_append hprefix tailTrace_4120746
  have hstable : (prefixWord ++ tailWord_4120746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4120746).length < 2 ^ (prefixWord ++ tailWord_4120746).sum := by decide
  have hdescent : baseEnd_4120746 < baseStart_4120746 := by decide
  rcases family_descends (prefixWord ++ tailWord_4120746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4120768 : List Nat := [2, 1, 1, 2, 5, 1, 2, 1, 4, 1, 3]
def baseStart_4120768 : Nat := 118140960795 + 4120768 * 2 ^ 59
def prefixEnd_4120768 : Nat := 4983230072969 + 3 ^ 40 * 4120768 * 2
def baseEnd_4120768 : Nat := 2115934649666638709948939

theorem tailTrace_4120768 : CollatzResearch.WordTrace tailWord_4120768 prefixEnd_4120768 2115934649666638709948939 := by
  unfold tailWord_4120768
  simp only [CollatzResearch.WordTrace]
  refine ⟨75148378167584390994713479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100197837556779187992951305 75148378167584390994713479)
  ·
    refine ⟨112722567251376586492070219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75148378167584390994713479 112722567251376586492070219)
    ·
      refine ⟨169083850877064879738105329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112722567251376586492070219 169083850877064879738105329)
      ·
        refine ⟨126812888157798659803578997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 169083850877064879738105329 126812888157798659803578997)
        ·
          refine ⟨11888708264793624356585531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 126812888157798659803578997 11888708264793624356585531)
          ·
            refine ⟨17833062397190436534878297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11888708264793624356585531 17833062397190436534878297)
            ·
              refine ⟨13374796797892827401158723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17833062397190436534878297 13374796797892827401158723)
              ·
                refine ⟨20062195196839241101738085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13374796797892827401158723 20062195196839241101738085)
                ·
                  refine ⟨3761661599407357706575891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20062195196839241101738085 3761661599407357706575891)
                  ·
                    refine ⟨5642492399111036559863837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3761661599407357706575891 5642492399111036559863837)
                    ·
                      refine ⟨2115934649666638709948939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5642492399111036559863837 2115934649666638709948939)
                      ·
                        rfl

theorem cell23_4120768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 2, 1, 4, 1, 3].length) (baseStart_4120768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4120768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4120768 prefixEnd_4120768 := by exact prefixLift 4120768
  have htrace : WordTrace (prefixWord ++ tailWord_4120768) baseStart_4120768 baseEnd_4120768 := by
    simpa [prefixWord, tailWord_4120768, baseEnd_4120768] using wordTrace_append hprefix tailTrace_4120768
  have hstable : (prefixWord ++ tailWord_4120768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4120768).length < 2 ^ (prefixWord ++ tailWord_4120768).sum := by decide
  have hdescent : baseEnd_4120768 < baseStart_4120768 := by decide
  rcases family_descends (prefixWord ++ tailWord_4120768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4120769 : List Nat := [1, 2, 6, 1, 2, 2, 1, 1, 3, 2, 2]
def baseStart_4120769 : Nat := 118140960795 + 4120769 * 2 ^ 59
def prefixEnd_4120769 : Nat := 4983230072969 + 3 ^ 40 * 4120769 * 2
def baseEnd_4120769 : Nat := 2115935163147293206036435

theorem tailTrace_4120769 : CollatzResearch.WordTrace tailWord_4120769 prefixEnd_4120769 2115935163147293206036435 := by
  unfold tailWord_4120769
  simp only [CollatzResearch.WordTrace]
  refine ⟨150296792808165159160213361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100197861872110106106808907 150296792808165159160213361)
  ·
    refine ⟨112722594606123869370160021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150296792808165159160213361 112722594606123869370160021)
    ·
      refine ⟨5283871622162056376726251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 112722594606123869370160021 5283871622162056376726251)
      ·
        refine ⟨7925807433243084565089377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5283871622162056376726251 7925807433243084565089377)
        ·
          refine ⟨5944355574932313423817033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7925807433243084565089377 5944355574932313423817033)
          ·
            refine ⟨4458266681199235067862775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5944355574932313423817033 4458266681199235067862775)
            ·
              refine ⟨6687400021798852601794163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4458266681199235067862775 6687400021798852601794163)
              ·
                refine ⟨10031100032698278902691245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6687400021798852601794163 10031100032698278902691245)
                ·
                  refine ⟨3761662512261854588509217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10031100032698278902691245 3761662512261854588509217)
                  ·
                    refine ⟨2821246884196390941381913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3761662512261854588509217 2821246884196390941381913)
                    ·
                      refine ⟨2115935163147293206036435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2821246884196390941381913 2115935163147293206036435)
                      ·
                        rfl

theorem cell23_4120769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 2, 1, 1, 3, 2, 2].length) (baseStart_4120769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4120769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4120769 prefixEnd_4120769 := by exact prefixLift 4120769
  have htrace : WordTrace (prefixWord ++ tailWord_4120769) baseStart_4120769 baseEnd_4120769 := by
    simpa [prefixWord, tailWord_4120769, baseEnd_4120769] using wordTrace_append hprefix tailTrace_4120769
  have hstable : (prefixWord ++ tailWord_4120769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4120769).length < 2 ^ (prefixWord ++ tailWord_4120769).sum := by decide
  have hdescent : baseEnd_4120769 < baseStart_4120769 := by decide
  rcases family_descends (prefixWord ++ tailWord_4120769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4120778 : List Nat := [3, 1, 2, 1, 3, 1, 2, 2, 3, 3, 2]
def baseStart_4120778 : Nat := 118140960795 + 4120778 * 2 ^ 59
def prefixEnd_4120778 : Nat := 4983230072969 + 3 ^ 40 * 4120778 * 2
def baseEnd_4120778 : Nat := 2115939784473183670823893

theorem tailTrace_4120778 : CollatzResearch.WordTrace tailWord_4120778 prefixEnd_4120778 2115939784473183670823893 := by
  unfold tailWord_4120778
  simp only [CollatzResearch.WordTrace]
  refine ⟨37574280266283138424322747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100198080710088369131527325 37574280266283138424322747)
  ·
    refine ⟨56361420399424707636484121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37574280266283138424322747 56361420399424707636484121)
    ·
      refine ⟨42271065299568530727363091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56361420399424707636484121 42271065299568530727363091)
      ·
        refine ⟨63406597949352796091044637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42271065299568530727363091 63406597949352796091044637)
        ·
          refine ⟨23777474231007298534141739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63406597949352796091044637 23777474231007298534141739)
          ·
            refine ⟨35666211346510947801212609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23777474231007298534141739 35666211346510947801212609)
            ·
              refine ⟨26749658509883210850909457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35666211346510947801212609 26749658509883210850909457)
              ·
                refine ⟨20062243882412408138182093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26749658509883210850909457 20062243882412408138182093)
                ·
                  refine ⟨7523341455904653051818285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20062243882412408138182093 7523341455904653051818285)
                  ·
                    refine ⟨2821253045964244894431857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7523341455904653051818285 2821253045964244894431857)
                    ·
                      refine ⟨2115939784473183670823893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2821253045964244894431857 2115939784473183670823893)
                      ·
                        rfl

theorem cell23_4120778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 2, 2, 3, 3, 2].length) (baseStart_4120778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4120778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4120778 prefixEnd_4120778 := by exact prefixLift 4120778
  have htrace : WordTrace (prefixWord ++ tailWord_4120778) baseStart_4120778 baseEnd_4120778 := by
    simpa [prefixWord, tailWord_4120778, baseEnd_4120778] using wordTrace_append hprefix tailTrace_4120778
  have hstable : (prefixWord ++ tailWord_4120778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4120778).length < 2 ^ (prefixWord ++ tailWord_4120778).sum := by decide
  have hdescent : baseEnd_4120778 < baseStart_4120778 := by decide
  rcases family_descends (prefixWord ++ tailWord_4120778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4120785 : List Nat := [1, 2, 2, 1, 2, 2, 6, 1, 2, 1, 3]
def baseStart_4120785 : Nat := 118140960795 + 4120785 * 2 ^ 59
def prefixEnd_4120785 : Nat := 4983230072969 + 3 ^ 40 * 4120785 * 2
def baseEnd_4120785 : Nat := 2115943378837765143436361

theorem tailTrace_4120785 : CollatzResearch.WordTrace tailWord_4120785 prefixEnd_4120785 2115943378837765143436361 := by
  unfold tailWord_4120785
  simp only [CollatzResearch.WordTrace]
  refine ⟨150297376376107193892795809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100198250917404795928530539 150297376376107193892795809)
  ·
    refine ⟨112723032282080395419596857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150297376376107193892795809 112723032282080395419596857)
    ·
      refine ⟨84542274211560296564697643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112723032282080395419596857 84542274211560296564697643)
      ·
        refine ⟨126813411317340444847046465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84542274211560296564697643 126813411317340444847046465)
        ·
          refine ⟨95110058488005333635284849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126813411317340444847046465 95110058488005333635284849)
          ·
            refine ⟨71332543866004000226463637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95110058488005333635284849 71332543866004000226463637)
            ·
              refine ⟨3343712993718937510615483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 71332543866004000226463637 3343712993718937510615483)
              ·
                refine ⟨5015569490578406265923225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3343712993718937510615483 5015569490578406265923225)
                ·
                  refine ⟨3761677117933804699442419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5015569490578406265923225 3761677117933804699442419)
                  ·
                    refine ⟨5642515676900707049163629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3761677117933804699442419 5642515676900707049163629)
                    ·
                      refine ⟨2115943378837765143436361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5642515676900707049163629 2115943378837765143436361)
                      ·
                        rfl

theorem cell23_4120785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 6, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 6, 1, 2, 1, 3].length) (baseStart_4120785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4120785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4120785 prefixEnd_4120785 := by exact prefixLift 4120785
  have htrace : WordTrace (prefixWord ++ tailWord_4120785) baseStart_4120785 baseEnd_4120785 := by
    simpa [prefixWord, tailWord_4120785, baseEnd_4120785] using wordTrace_append hprefix tailTrace_4120785
  have hstable : (prefixWord ++ tailWord_4120785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4120785).length < 2 ^ (prefixWord ++ tailWord_4120785).sum := by decide
  have hdescent : baseEnd_4120785 < baseStart_4120785 := by decide
  rcases family_descends (prefixWord ++ tailWord_4120785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4120808 : List Nat := [2, 1, 4, 1, 2, 2, 1, 1, 3, 4, 2]
def baseStart_4120808 : Nat := 118140960795 + 4120808 * 2 ^ 59
def prefixEnd_4120808 : Nat := 4983230072969 + 3 ^ 40 * 4120808 * 2
def baseEnd_4120808 : Nat := 2115955188892818553448755

theorem tailTrace_4120808 : CollatzResearch.WordTrace tailWord_4120808 prefixEnd_4120808 2115955188892818553448755 := by
  unfold tailWord_4120808
  simp only [CollatzResearch.WordTrace]
  refine ⟨75149107627511934410441539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100198810170015912547255385 75149107627511934410441539)
  ·
    refine ⟨112723661441267901615662309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75149107627511934410441539 112723661441267901615662309)
    ·
      refine ⟨21135686520237731552936683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 112723661441267901615662309 21135686520237731552936683)
      ·
        refine ⟨31703529780356597329405025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21135686520237731552936683 31703529780356597329405025)
        ·
          refine ⟨23777647335267447997053769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31703529780356597329405025 23777647335267447997053769)
          ·
            refine ⟨17833235501450585997790327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23777647335267447997053769 17833235501450585997790327)
            ·
              refine ⟨26749853252175878996685491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17833235501450585997790327 26749853252175878996685491)
              ·
                refine ⟨40124779878263818495028237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26749853252175878996685491 40124779878263818495028237)
                ·
                  refine ⟨15046792454348931935635589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40124779878263818495028237 15046792454348931935635589)
                  ·
                    refine ⟨2821273585190424737931673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15046792454348931935635589 2821273585190424737931673)
                    ·
                      refine ⟨2115955188892818553448755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2821273585190424737931673 2115955188892818553448755)
                      ·
                        rfl

theorem cell23_4120808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 1, 1, 3, 4, 2].length) (baseStart_4120808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4120808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4120808 prefixEnd_4120808 := by exact prefixLift 4120808
  have htrace : WordTrace (prefixWord ++ tailWord_4120808) baseStart_4120808 baseEnd_4120808 := by
    simpa [prefixWord, tailWord_4120808, baseEnd_4120808] using wordTrace_append hprefix tailTrace_4120808
  have hstable : (prefixWord ++ tailWord_4120808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4120808).length < 2 ^ (prefixWord ++ tailWord_4120808).sum := by decide
  have hdescent : baseEnd_4120808 < baseStart_4120808 := by decide
  rcases family_descends (prefixWord ++ tailWord_4120808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4120824 : List Nat := [2, 1, 2, 1, 1, 2, 1, 3, 1, 2, 7]
def baseStart_4120824 : Nat := 118140960795 + 4120824 * 2 ^ 59
def prefixEnd_4120824 : Nat := 4983230072969 + 3 ^ 40 * 4120824 * 2
def baseEnd_4120824 : Nat := 2115963404583290490848681

theorem tailTrace_4120824 : CollatzResearch.WordTrace tailWord_4120824 prefixEnd_4120824 2115963404583290490848681 := by
  unfold tailWord_4120824
  simp only [CollatzResearch.WordTrace]
  refine ⟨75149399411482951776732763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100199199215310602368977017 75149399411482951776732763)
  ·
    refine ⟨112724099117224427665099145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75149399411482951776732763 112724099117224427665099145)
    ·
      refine ⟨84543074337918320748824359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112724099117224427665099145 84543074337918320748824359)
      ·
        refine ⟨126814611506877481123236539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84543074337918320748824359 126814611506877481123236539)
        ·
          refine ⟨190221917260316221684854809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126814611506877481123236539 190221917260316221684854809)
          ·
            refine ⟨142666437945237166263641107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 190221917260316221684854809 142666437945237166263641107)
            ·
              refine ⟨213999656917855749395461661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 142666437945237166263641107 213999656917855749395461661)
              ·
                refine ⟨80249871344195906023298123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 213999656917855749395461661 80249871344195906023298123)
                ·
                  refine ⟨120374807016293859034947185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 80249871344195906023298123 120374807016293859034947185)
                  ·
                    refine ⟨90281105262220394276210389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 120374807016293859034947185 90281105262220394276210389)
                    ·
                      refine ⟨2115963404583290490848681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 90281105262220394276210389 2115963404583290490848681)
                      ·
                        rfl

theorem cell23_4120824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 3, 1, 2, 7].length) (baseStart_4120824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4120824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4120824 prefixEnd_4120824 := by exact prefixLift 4120824
  have htrace : WordTrace (prefixWord ++ tailWord_4120824) baseStart_4120824 baseEnd_4120824 := by
    simpa [prefixWord, tailWord_4120824, baseEnd_4120824] using wordTrace_append hprefix tailTrace_4120824
  have hstable : (prefixWord ++ tailWord_4120824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4120824).length < 2 ^ (prefixWord ++ tailWord_4120824).sum := by decide
  have hdescent : baseEnd_4120824 < baseStart_4120824 := by decide
  rcases family_descends (prefixWord ++ tailWord_4120824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4120841 : List Nat := [1, 2, 1, 1, 3, 4, 1, 1, 1, 5, 3]
def baseStart_4120841 : Nat := 118140960795 + 4120841 * 2 ^ 59
def prefixEnd_4120841 : Nat := 4983230072969 + 3 ^ 40 * 4120841 * 2
def baseEnd_4120841 : Nat := 2115972133754416924336103

theorem tailTrace_4120841 : CollatzResearch.WordTrace tailWord_4120841 prefixEnd_4120841 2115972133754416924336103 := by
  unfold tailWord_4120841
  simp only [CollatzResearch.WordTrace]
  refine ⟨150299418863904315456834377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100199612575936210304556251 150299418863904315456834377)
  ·
    refine ⟨112724564147928236592625783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150299418863904315456834377 112724564147928236592625783)
    ·
      refine ⟨169086846221892354888938675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112724564147928236592625783 169086846221892354888938675)
      ·
        refine ⟨253630269332838532333408013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169086846221892354888938675 253630269332838532333408013)
        ·
          refine ⟨95111350999814449625028005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 253630269332838532333408013 95111350999814449625028005)
          ·
            refine ⟨17833378312465209304692751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 95111350999814449625028005 17833378312465209304692751)
            ·
              refine ⟨26750067468697813957039127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17833378312465209304692751 26750067468697813957039127)
              ·
                refine ⟨40125101203046720935558691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26750067468697813957039127 40125101203046720935558691)
                ·
                  refine ⟨60187651804570081403338037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40125101203046720935558691 60187651804570081403338037)
                  ·
                    refine ⟨5642592356678445131562941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 60187651804570081403338037 5642592356678445131562941)
                    ·
                      refine ⟨2115972133754416924336103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5642592356678445131562941 2115972133754416924336103)
                      ·
                        rfl

theorem cell23_4120841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 1, 1, 1, 5, 3].length) (baseStart_4120841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4120841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4120841 prefixEnd_4120841 := by exact prefixLift 4120841
  have htrace : WordTrace (prefixWord ++ tailWord_4120841) baseStart_4120841 baseEnd_4120841 := by
    simpa [prefixWord, tailWord_4120841, baseEnd_4120841] using wordTrace_append hprefix tailTrace_4120841
  have hstable : (prefixWord ++ tailWord_4120841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4120841).length < 2 ^ (prefixWord ++ tailWord_4120841).sum := by decide
  have hdescent : baseEnd_4120841 < baseStart_4120841 := by decide
  rcases family_descends (prefixWord ++ tailWord_4120841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4120908 : List Nat := [2, 2, 1, 3, 2, 1, 1, 4, 3, 4]
def baseStart_4120908 : Nat := 118140960795 + 4120908 * 2 ^ 59
def prefixEnd_4120908 : Nat := 4983230072969 + 3 ^ 40 * 4120908 * 2
def baseEnd_4120908 : Nat := 705335512319422720732765

theorem tailTrace_4120908 : CollatzResearch.WordTrace tailWord_4120908 prefixEnd_4120908 705335512319422720732765 := by
  unfold tailWord_4120908
  simp only [CollatzResearch.WordTrace]
  refine ⟨75150931277330792949761689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100201241703107723933015585 75150931277330792949761689)
  ·
    refine ⟨56363198457998094712321267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75150931277330792949761689 56363198457998094712321267)
    ·
      refine ⟨84544797686997142068481901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56363198457998094712321267 84544797686997142068481901)
      ·
        refine ⟨31704299132623928275680713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84544797686997142068481901 31704299132623928275680713)
        ·
          refine ⟨23778224349467946206760535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31704299132623928275680713 23778224349467946206760535)
          ·
            refine ⟨35667336524201919310140803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23778224349467946206760535 35667336524201919310140803)
            ·
              refine ⟨53501004786302878965211205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35667336524201919310140803 53501004786302878965211205)
              ·
                refine ⟨10031438397431789805977101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53501004786302878965211205 10031438397431789805977101)
                ·
                  refine ⟨3761789399036921177241413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10031438397431789805977101 3761789399036921177241413)
                  ·
                    refine ⟨705335512319422720732765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3761789399036921177241413 705335512319422720732765)
                    ·
                      rfl

theorem cell23_4120908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 4, 3, 4].length) (baseStart_4120908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4120908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4120908 prefixEnd_4120908 := by exact prefixLift 4120908
  have htrace : WordTrace (prefixWord ++ tailWord_4120908) baseStart_4120908 baseEnd_4120908 := by
    simpa [prefixWord, tailWord_4120908, baseEnd_4120908] using wordTrace_append hprefix tailTrace_4120908
  have hstable : (prefixWord ++ tailWord_4120908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4120908).length < 2 ^ (prefixWord ++ tailWord_4120908).sum := by decide
  have hdescent : baseEnd_4120908 < baseStart_4120908 := by decide
  rcases family_descends (prefixWord ++ tailWord_4120908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4120935 : List Nat := [1, 1, 5, 1, 3, 2, 1, 2, 2, 2, 3]
def baseStart_4120935 : Nat := 118140960795 + 4120935 * 2 ^ 59
def prefixEnd_4120935 : Nat := 4983230072969 + 3 ^ 40 * 4120935 * 2
def baseEnd_4120935 : Nat := 2116020400935939556560671

theorem tailTrace_4120935 : CollatzResearch.WordTrace tailWord_4120935 prefixEnd_4120935 2116020400935939556560671 := by
  unfold tailWord_4120935
  simp only [CollatzResearch.WordTrace]
  refine ⟨150302847325563769510756259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100201898217042513007170839 150302847325563769510756259)
  ·
    refine ⟨225454270988345654266134389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150302847325563769510756259 225454270988345654266134389)
    ·
      refine ⟨21136337905157405087450099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 225454270988345654266134389 21136337905157405087450099)
      ·
        refine ⟨31704506857736107631175149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21136337905157405087450099 31704506857736107631175149)
        ·
          refine ⟨11889190071651040361690681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31704506857736107631175149 11889190071651040361690681)
          ·
            refine ⟨8916892553738280271268011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11889190071651040361690681 8916892553738280271268011)
            ·
              refine ⟨13375338830607420406902017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8916892553738280271268011 13375338830607420406902017)
              ·
                refine ⟨10031504122955565305176513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13375338830607420406902017 10031504122955565305176513)
                ·
                  refine ⟨7523628092216673978882385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10031504122955565305176513 7523628092216673978882385)
                  ·
                    refine ⟨5642721069162505484161789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7523628092216673978882385 5642721069162505484161789)
                    ·
                      refine ⟨2116020400935939556560671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5642721069162505484161789 2116020400935939556560671)
                      ·
                        rfl

theorem cell23_4120935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 1, 2, 2, 2, 3].length) (baseStart_4120935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4120935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4120935 prefixEnd_4120935 := by exact prefixLift 4120935
  have htrace : WordTrace (prefixWord ++ tailWord_4120935) baseStart_4120935 baseEnd_4120935 := by
    simpa [prefixWord, tailWord_4120935, baseEnd_4120935] using wordTrace_append hprefix tailTrace_4120935
  have hstable : (prefixWord ++ tailWord_4120935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4120935).length < 2 ^ (prefixWord ++ tailWord_4120935).sum := by decide
  have hdescent : baseEnd_4120935 < baseStart_4120935 := by decide
  rcases family_descends (prefixWord ++ tailWord_4120935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4120938 : List Nat := [3, 1, 3, 3, 1, 1, 2, 1, 8]
def baseStart_4120938 : Nat := 118140960795 + 4120938 * 2 ^ 59
def prefixEnd_4120938 : Nat := 4983230072969 + 3 ^ 40 * 4120938 * 2
def baseEnd_4120938 : Nat := 235113549041989227202573

theorem tailTrace_4120938 : CollatzResearch.WordTrace tailWord_4120938 prefixEnd_4120938 235113549041989227202573 := by
  unfold tailWord_4120938
  simp only [CollatzResearch.WordTrace]
  refine ⟨37575739186138225255778867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100201971163035267348743645 37575739186138225255778867)
  ·
    refine ⟨56363608779207337883668301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37575739186138225255778867 56363608779207337883668301)
    ·
      refine ⟨21136353292202751706375613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56363608779207337883668301 21136353292202751706375613)
      ·
        refine ⟨7926132484576031889890855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21136353292202751706375613 7926132484576031889890855)
        ·
          refine ⟨11889198726864047834836283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7926132484576031889890855 11889198726864047834836283)
          ·
            refine ⟨17833798090296071752254425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11889198726864047834836283 17833798090296071752254425)
            ·
              refine ⟨13375348567722053814190819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17833798090296071752254425 13375348567722053814190819)
              ·
                refine ⟨20063022851583080721286229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13375348567722053814190819 20063022851583080721286229)
                ·
                  refine ⟨235113549041989227202573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 20063022851583080721286229 235113549041989227202573)
                  ·
                    rfl

theorem cell23_4120938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 2, 1, 8].length) (baseStart_4120938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4120938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4120938 prefixEnd_4120938 := by exact prefixLift 4120938
  have htrace : WordTrace (prefixWord ++ tailWord_4120938) baseStart_4120938 baseEnd_4120938 := by
    simpa [prefixWord, tailWord_4120938, baseEnd_4120938] using wordTrace_append hprefix tailTrace_4120938
  have hstable : (prefixWord ++ tailWord_4120938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4120938).length < 2 ^ (prefixWord ++ tailWord_4120938).sum := by decide
  have hdescent : baseEnd_4120938 < baseStart_4120938 := by decide
  rcases family_descends (prefixWord ++ tailWord_4120938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4120955 : List Nat := [1, 1, 1, 1, 1, 9, 2, 1, 6]
def baseStart_4120955 : Nat := 118140960795 + 4120955 * 2 ^ 59
def prefixEnd_4120955 : Nat := 4983230072969 + 3 ^ 40 * 4120955 * 2
def baseEnd_4120955 : Nat := 235114518949892164256731

theorem tailTrace_4120955 : CollatzResearch.WordTrace tailWord_4120955 prefixEnd_4120955 235114518949892164256731 := by
  unfold tailWord_4120955
  simp only [CollatzResearch.WordTrace]
  refine ⟨150303576785491312926484319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100202384523660875284322879 150303576785491312926484319)
  ·
    refine ⟨225455365178236969389726479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150303576785491312926484319 225455365178236969389726479)
    ·
      refine ⟨338183047767355454084589719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225455365178236969389726479 338183047767355454084589719)
      ·
        refine ⟨507274571651033181126884579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 338183047767355454084589719 507274571651033181126884579)
        ·
          refine ⟨760911857476549771690326869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 507274571651033181126884579 760911857476549771690326869)
          ·
            refine ⟨4458467914901658818498009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 760911857476549771690326869 4458467914901658818498009)
            ·
              refine ⟨3343850936176244113873507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4458467914901658818498009 3343850936176244113873507)
              ·
                refine ⟨5015776404264366170810261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3343850936176244113873507 5015776404264366170810261)
                ·
                  refine ⟨235114518949892164256731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5015776404264366170810261 235114518949892164256731)
                  ·
                    rfl

theorem cell23_4120955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 9, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 9, 2, 1, 6].length) (baseStart_4120955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4120955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4120955 prefixEnd_4120955 := by exact prefixLift 4120955
  have htrace : WordTrace (prefixWord ++ tailWord_4120955) baseStart_4120955 baseEnd_4120955 := by
    simpa [prefixWord, tailWord_4120955, baseEnd_4120955] using wordTrace_append hprefix tailTrace_4120955
  have hstable : (prefixWord ++ tailWord_4120955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4120955).length < 2 ^ (prefixWord ++ tailWord_4120955).sum := by decide
  have hdescent : baseEnd_4120955 < baseStart_4120955 := by decide
  rcases family_descends (prefixWord ++ tailWord_4120955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4120968 : List Nat := [2, 1, 3, 3, 1, 1, 3, 1, 3, 5]
def baseStart_4120968 : Nat := 118140960795 + 4120968 * 2 ^ 59
def prefixEnd_4120968 : Nat := 4983230072969 + 3 ^ 40 * 4120968 * 2
def baseEnd_4120968 : Nat := 705345781932512642482673

theorem tailTrace_4120968 : CollatzResearch.WordTrace tailWord_4120968 prefixEnd_4120968 705345781932512642482673 := by
  unfold tailWord_4120968
  simp only [CollatzResearch.WordTrace]
  refine ⟨75152025467222108073353779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100202700622962810764471705 75152025467222108073353779)
  ·
    refine ⟨112728038200833162110030669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75152025467222108073353779 112728038200833162110030669)
    ·
      refine ⟨42273014325312435791261501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 112728038200833162110030669 42273014325312435791261501)
      ·
        refine ⟨15852380371992163421723063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42273014325312435791261501 15852380371992163421723063)
        ·
          refine ⟨23778570557988245132584595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15852380371992163421723063 23778570557988245132584595)
          ·
            refine ⟨35667855836982367698876893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23778570557988245132584595 35667855836982367698876893)
            ·
              refine ⟨13375445938868387887078835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35667855836982367698876893 13375445938868387887078835)
              ·
                refine ⟨20063168908302581830618253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13375445938868387887078835 20063168908302581830618253)
                ·
                  refine ⟨7523688340613468186481845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20063168908302581830618253 7523688340613468186481845)
                  ·
                    refine ⟨705345781932512642482673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7523688340613468186481845 705345781932512642482673)
                    ·
                      rfl

theorem cell23_4120968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 3, 1, 3, 5].length) (baseStart_4120968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4120968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4120968 prefixEnd_4120968 := by exact prefixLift 4120968
  have htrace : WordTrace (prefixWord ++ tailWord_4120968) baseStart_4120968 baseEnd_4120968 := by
    simpa [prefixWord, tailWord_4120968, baseEnd_4120968] using wordTrace_append hprefix tailTrace_4120968
  have hstable : (prefixWord ++ tailWord_4120968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4120968).length < 2 ^ (prefixWord ++ tailWord_4120968).sum := by decide
  have hdescent : baseEnd_4120968 < baseStart_4120968 := by decide
  rcases family_descends (prefixWord ++ tailWord_4120968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4120985 : List Nat := [1, 2, 1, 2, 1, 4, 5, 1, 1, 5]
def baseStart_4120985 : Nat := 118140960795 + 4120985 * 2 ^ 59
def prefixEnd_4120985 : Nat := 4983230072969 + 3 ^ 40 * 4120985 * 2
def baseEnd_4120985 : Nat := 705348691656221453645147

theorem tailTrace_4120985 : CollatzResearch.WordTrace tailWord_4120985 prefixEnd_4120985 705348691656221453645147 := by
  unfold tailWord_4120985
  simp only [CollatzResearch.WordTrace]
  refine ⟨150304670975382628050076409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100203113983588418700050939 150304670975382628050076409)
  ·
    refine ⟨112728503231536971037557307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150304670975382628050076409 112728503231536971037557307)
    ·
      refine ⟨169092754847305456556335961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112728503231536971037557307 169092754847305456556335961)
      ·
        refine ⟨126819566135479092417251971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 169092754847305456556335961 126819566135479092417251971)
        ·
          refine ⟨190229349203218638625877957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126819566135479092417251971 190229349203218638625877957)
          ·
            refine ⟨35668002975603494742352117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 190229349203218638625877957 35668002975603494742352117)
            ·
              refine ⟨3343875278962827632095511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 35668002975603494742352117 3343875278962827632095511)
              ·
                refine ⟨5015812918444241448143267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3343875278962827632095511 5015812918444241448143267)
                ·
                  refine ⟨7523719377666362172214901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5015812918444241448143267 7523719377666362172214901)
                  ·
                    refine ⟨705348691656221453645147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7523719377666362172214901 705348691656221453645147)
                    ·
                      rfl

theorem cell23_4120985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 5, 1, 1, 5].length) (baseStart_4120985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4120985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4120985 prefixEnd_4120985 := by exact prefixLift 4120985
  have htrace : WordTrace (prefixWord ++ tailWord_4120985) baseStart_4120985 baseEnd_4120985 := by
    simpa [prefixWord, tailWord_4120985, baseEnd_4120985] using wordTrace_append hprefix tailTrace_4120985
  have hstable : (prefixWord ++ tailWord_4120985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4120985).length < 2 ^ (prefixWord ++ tailWord_4120985).sum := by decide
  have hdescent : baseEnd_4120985 < baseStart_4120985 := by decide
  rcases family_descends (prefixWord ++ tailWord_4120985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
